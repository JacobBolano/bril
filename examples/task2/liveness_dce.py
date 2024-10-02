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


def cfg_union_maps(successor_facts):
    # set union
    output = set()

    for fact in successor_facts:
        output = output.union(fact)
    return output

def cfg_local_analysis(out_map_current, block):
    
    new_facts = copy.deepcopy(out_map_current)

    for instr in reversed(block):
        # Remove kill(b) from our facts
        if "dest" in instr:
            dest = instr["dest"]
            new_facts.discard(dest)

        if "args" in instr:
            args = instr["args"]
            for arg in args:
                new_facts.add(arg)
    
    return new_facts
 

def dataflow_analysis(instructions):        
    blocks, label_to_block = instruct_to_blocks(instructions)
    cfg = create_cfg(blocks, label_to_block)

    # fact: empty map
    in_map = [set() for _ in range(len(blocks))]
    out_map = [set() for _ in range(len(blocks))]

    worklist = list(range(len(blocks)))

    while worklist:
        # going backwards so we pop from the last element
        current = worklist.pop()
        block = blocks[current]

        # merge: A way to relate the input/output facts of a block to the inputs/outputs of its neighbors.
        # we are merging from the in maps of successors (backwards)
        successor_facts = [in_map[s] for s in cfg[current]["successors"]]
        logging.debug(f"successor_facts at block {current} with successors {cfg[current]['successors']}: {successor_facts}")  
        # we merge (union) the in facts of the successor blocks to find our current out  
        out_map[current] = cfg_union_maps(successor_facts)

        # we then find the in map by performing our transfer analysis
        new_facts = cfg_local_analysis(out_map[current], block)   
        logging.debug(f"new facts at block {current} with predecessors {cfg[current]['predecessors']}: {new_facts}")    

        # we check if the input has changed and if so, we update predecessors
        if in_map[current] != new_facts:
            in_map[current] = new_facts
            worklist.extend(cfg[current]["predecessors"])
    
    # update our blocks by performing a better version of DCE
    updated_blocks = super_dead_code_eliminator(in_map, out_map, blocks)
    show_maps(in_map, out_map, updated_blocks)
    return rebuild_instructions(updated_blocks)

def super_dead_code_eliminator(in_map, out_map, blocks):
    updated_blocks = []
    for i,block in enumerate(blocks):
        current_outs = copy.deepcopy(out_map[i])
        updated_block = copy.deepcopy(block)

        for instr in reversed(block):
            if "dest" in instr:
                # we are assigning something
                dest = instr["dest"]
                # dead code if dest not in the current_outs
                if dest not in current_outs:
                    updated_block.remove(instr)
                current_outs.discard(dest)

            if "args" in instr:
                args = instr["args"]
                for arg in args:
                    current_outs.add(arg)
        
        updated_blocks.append(updated_block)
    return updated_blocks

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