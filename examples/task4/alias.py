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

    return cfg

def transfer_analysis(in_map_current, block, block_index):
    # input: in_map_current - map of facts at the beginning of the block
    # output: new_facts - map of facts at the end of the block
    new_facts = copy.deepcopy(in_map_current) if in_map_current else {}
    # logging.debug(f"new facts: {new_facts}")
    for instr_index, instr in enumerate(block):
       
       if "dest" in instr:
            var = instr["dest"]
            if "op" in instr and instr["op"] in {"alloc", "id", "ptradd", "load"}:
                if var not in new_facts:
                    new_facts[var] = set()
                if instr["op"] == "alloc":
                    new_facts[var].add((block_index, instr_index))
                elif instr["op"] == "id" and "ptr" in instr["type"]:
                    # logging.debug(f"potential alias for instruction {instr}")
                    if instr["args"][0] in new_facts:
                        new_facts[var].update(new_facts[instr["args"][0]])
                elif instr["op"] == "ptradd":
                    # logging.debug(f"potential alias for instruction {instr} and facts are {in_map_current}")
                    if instr["args"][0] in new_facts:
                        new_facts[var].update(new_facts[instr["args"][0]])
                elif instr["op"] == "load":
                    new_facts[var].add("all_memory_locations")

    return new_facts

def merge(predecessor_facts):
    # merge facts
    if not predecessor_facts:
        return {}
    # check if any of the predecessor facts are empty
    # if any(d == {} for d in predecessor_facts):
    #     return {}
    
    output = {}

    for fact in predecessor_facts:
        for key, value in fact.items():
            # if we already saw this key before
            if key in output:
                # otherwise we keep it
                output[key].update(value)
            else:
                # add to the map
                output[key] = value
    return output

def dataflow_analysis(instructions, arguments):      
    arg_names = [argument["name"] for argument in arguments] if arguments else []  
    blocks, label_to_block = instruct_to_blocks(instructions)
    cfg = create_cfg(blocks, label_to_block)

    # we don't know anything about the incoming function arguments
    # Ensure that our analysis is something conservative: all function arguments pointing to all memory locations
    default_map_for_arguments = {arg: {"all_memory_locations"} for arg in arg_names}

    # fact: empty map
    in_map = [{} for _ in range(len(blocks))]
    out_map = [{} for _ in range(len(blocks))]
    
    worklist = list(range(len(blocks)))

    while worklist:
        current = worklist.pop(0)
        block = blocks[current]

        # merge: A way to relate the input/output facts of a block to the inputs/outputs of its neighbors.
        predecessor_facts = [out_map[p] for p in cfg[current]["predecessors"]]
        predecessor_facts.append(default_map_for_arguments) # we always need to make sure our variable names are accounted for conservatively
        # logging.debug(f"predecessor facts at block {current} with predecessors {cfg[current]['predecessors']}: {predecessor_facts}")    
        in_map[current] = merge(predecessor_facts)
        # logging.debug(f"merged facts {in_map[current]}")
        # transfer: A way to compute the fact at the end of a block from the facts at the beginning of the block.
        # we get new constants within current blocks based on our input map
        new_facts = transfer_analysis(in_map[current], block, current)
        # logging.debug(f"new facts at block {current} with sucessors {cfg[current]['successors']}: {new_facts}")    

        # we check if the output has changed and if so, we update and add the sucessors the worklist
        if out_map[current] != new_facts:
            out_map[current] = new_facts
            worklist.extend(cfg[current]["successors"])
    
    logging.debug(f"in map {in_map}")
    logging.debug(f"out map {out_map}")

    updated_blocks = dead_store_elimination(blocks, in_map, out_map)

    return rebuild_instructions(updated_blocks)

def dead_store_elimination(blocks, in_map, out_map):
    updated_blocks = []
    for i,block in enumerate(blocks):
        current_outs = copy.deepcopy(out_map[i])
        updated_block = copy.deepcopy(block)

        for instr in reversed(block):
            # check if the instruction is a store at an address that might alias
            if "op" in instr and instr["op"] == "store":
                target_store = instr["args"][0]
                # logging.debug(f"target store {target_store}")

                alias = False
                for var, memory_locations in current_outs.items():
                    if var == target_store:
                        continue
                    if "all_memory_locations" in memory_locations:
                        alias = True
                    if current_outs[target_store] & memory_locations:
                        alias = True
                if not alias and "STORED" in current_outs[target_store]:
                    logging.debug(f"deleting {instr} as alias is {alias} outs for this is at {current_outs[target_store]}")
                    updated_block.remove(instr)
                else:
                    # our variable is in current outs but we are storing it.
                    current_outs[target_store].add("STORED")

        updated_blocks.append(updated_block)
    return updated_blocks

def rebuild_instructions(blocks):
    output = []
    for block in blocks:
        for instr in block:
            output.append(instr)
    return output
                    
if __name__ == "__main__":
    prog = json.load(sys.stdin)

    for fn in prog["functions"]:
        fn["instrs"] = dataflow_analysis(fn["instrs"], fn["args"] if "args" in fn else None) 
    json.dump(prog, sys.stdout, indent=2)