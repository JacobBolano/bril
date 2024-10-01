import json
import sys
import copy
import logging
from collections import defaultdict

logging.basicConfig(filename='debug.log', level=logging.DEBUG)
def check_jump(instr):
    return instr.get("op") in {"jmp", "br", "ret"}

def instruct_to_blocks(instructions):
    blocks = []
    current_block = []
    label_to_block = {}
    
    for i, instruction in enumerate(instructions):
        # If the instruction has a label, we start a new block
        if "label" in instruction:
            if current_block:
                blocks.append(current_block)

            # Start a new block with the label
            current_block = [instruction]
            label_to_block[instruction['label']] = len(blocks)  # Store the block index for this label
        else:
            # Add the instruction to the current block
            current_block.append(instruction)

            if check_jump(instruction):
                blocks.append(current_block)
                current_block = []

    if current_block:
        blocks.append(current_block)

    return blocks, label_to_block

def create_cfg(blocks, label_to_block):
    # logging.debug(f"blocks: {blocks}")
    cfg = defaultdict(lambda: {"predecessors": [], "successors": []})

    for i, block in enumerate(blocks):
        final_instr = block[-1]
        if "op" not in final_instr:
            # we just add it as the next
            if i < len(blocks) - 1:
                cfg[i]["successors"].append(i + 1)
                cfg[i + 1]["predecessors"].append(i)
        elif final_instr["op"] == "jmp":
            jmp_index = label_to_block[final_instr["labels"][0]]
            cfg[i]["successors"].append(jmp_index)
            cfg[jmp_index]['predecessors'].append(i)

        elif final_instr["op"] == "br":
            true_label, false_label = final_instr["labels"]
            true_block_index = label_to_block[true_label]
            false_block_index = label_to_block[false_label]

            cfg[i]["successors"].append(true_block_index)
            cfg[i]["successors"].append(false_block_index)

            cfg[true_block_index]["predecessors"].append(i)
            cfg[false_block_index]["predecessors"].append(i)

        elif final_instr["op"] == "ret":
            continue
        else:
            # we just add it as the next
            if i < len(blocks) - 1:
                cfg[i]["successors"].append(i + 1)
                cfg[i + 1]["predecessors"].append(i)

    # logging.debug(f"final cfg: {cfg}")

    return cfg

def constant_folder(op, args):
    if op == "add":
        return args[0] + args[1]
    elif op == "sub":
        return args[0] - args[1]
    elif op == "mul":
        return args[0] * args[1]
    elif op == "div" and args[1] != 0:
        # don't want to divide by 0
        return args[0] / args[1]
    elif op == "and":
        return args[0] and args[1]
    elif op == "eq":
        return args[0] == args[1]
    elif op == "lt":
        return args[0] < args[1]
    elif op == "gt":
        return args[0] > args[1]
    elif op == "le":
        return args[0] <= args[1]
    elif op == "ge":
        return args[0] >= args[1]
    # if we get a weird instruction
    return None
def cfg_local_analysis(in_map_current, block):
    # input: in_map_current - map of facts at the beginning of the block
    # output: new_facts - map of facts at the end of the block
    new_facts = copy.deepcopy(in_map_current) if in_map_current else {}
    # logging.debug(f"new facts: {new_facts}")
    for i, instr in enumerate(block):
        if "dest" in instr:
            if instr["op"] == "const":
                new_facts[instr["dest"]] = instr["value"]
            elif instr["op"] in {"add", "sub", "mul", "div", "and", "not", "eq", "lt", "gt", "le", "ge"}:
                # check that these arguments exist in new_facts and then check that they are real (not ?)
                if all(arg in new_facts for arg in instr['args']) and all(new_facts[arg] != '?' for arg in instr['args']):
                    constant_fold_result = constant_folder(instr["op"], [new_facts[x] for x in instr["args"]])
                    # update facts
                    new_facts[instr["dest"]] = constant_fold_result
                    # create new instruction
                    new_instruction = {}
                    new_instruction["op"] = "const"
                    new_instruction["type"] = "bool" if isinstance(constant_fold_result, bool) else "int"
                    new_instruction["value"] = constant_fold_result
                    new_instruction["dest"] = instr["dest"]

                    #update block
                    block[i] = new_instruction
                else:
                    new_facts[instr["dest"]] = '?'


            elif instr["op"] in {"not", "id"}:
                if instr['args'][0] in new_facts and new_facts[instr['args'][0]] != '?':
                    # check that these argument exists in new_facts and then check that it is real (not ?)
                    copied_value = new_facts[instr["args"][0]]
                    if instr['op'] == 'not':
                        copied_value = not copied_value
                    # update facts
                    new_facts[instr["dest"]] = copied_value
                    # create new instruction
                    new_instruction = {}
                    new_instruction["op"] = "const"
                    new_instruction["type"] = "bool" if isinstance(copied_value, bool) else "int"
                    new_instruction["value"] = copied_value
                    new_instruction["dest"] = instr["dest"]
                    
                    #update block
                    block[i] = new_instruction
                else:
                    new_facts[instr["dest"]] = '?'
            else:
                # we don't know what it is
                new_facts[instr["dest"]] = '?'

    return new_facts, block

def cfg_intersect_maps(predecessor_facts):
    # merge facts

    if not predecessor_facts:
        return {}
    
    # check if any of the predecessor facts are empty
    if any(d == {} for d in predecessor_facts):
        return {}
    
    potential_output = {}

    for fact in predecessor_facts:
        for key, value in fact.items():
            if value == '?':
                potential_output[key] = '?'
            else:
                # if we already saw this key before
                if key in potential_output:
                    # if the values are different, this variable is no longer constant
                    if potential_output[key] != value:
                        potential_output[key] = '?'
                    # otherwise we keep it
                else:
                    # add to the map
                    potential_output[key] = value
    return potential_output
    # final_output = {}
    # for fact in potential_output:
    #     if potential_output[fact] is not None:
    #         final_output[fact] = potential_output[fact]   

    # return final_output

def dataflow_analysis(instructions):        
    blocks, label_to_block = instruct_to_blocks(instructions)
    cfg = create_cfg(blocks, label_to_block)

    # fact: empty map
    in_map = [{} for _ in range(len(blocks))]
    out_map = [{} for _ in range(len(blocks))]

    worklist = list(range(len(blocks)))

    while worklist:
        current = worklist.pop(0)
        block = blocks[current]

        # merge: A way to relate the input/output facts of a block to the inputs/outputs of its neighbors.
        # we are merging from predecessors
        predecessor_facts = [out_map[p] for p in cfg[current]["predecessors"]]
        # logging.debug(f"predecessor facts at block {current} with predecessors {cfg[current]['predecessors']}: {predecessor_facts}")    
        in_map[current] = cfg_intersect_maps(predecessor_facts)

        # transfer: A way to compute the fact at the end of a block from the facts at the beginning of the block.
        # we get new constants within current blocks based on our input map
        new_facts, new_block = cfg_local_analysis(in_map[current], block)
        # logging.debug(f"new facts at block {current} with sucessors {cfg[current]['successors']}: {new_facts}")    

        # we check if the output has changed and if so, we update and add the sucessors the worklist
        if out_map[current] != new_facts:
            out_map[current] = new_facts
            worklist.extend(cfg[current]["successors"])
        
        # update the block
        blocks[current] = new_block
    show_maps(in_map, out_map, blocks)
    return rebuild_instructions(blocks)

# helper method to show maps in a nice way
def show_maps(in_map, out_map, blocks):
    for i, block in enumerate(blocks):
        if i == 0:
            logging.debug("Initial block")
        else:
            if 'label' in block[0]:
                logging.debug(f"{block[0]['label']}")
            else:
                logging.debug(f"{block[0]}")
        
        logging.debug(f"in: {in_map[i]}")
        logging.debug(f"out: {out_map[i]}")

def rebuild_instructions(blocks):
    output = []
    for block in blocks:
        for instr in block:
            output.append(instr)
    return output
                    
if __name__ == "__main__":
    prog = json.load(sys.stdin)

    for fn in prog["functions"]:
        fn["instrs"] = dataflow_analysis(fn["instrs"]) 
    json.dump(prog, sys.stdout, indent=2)
