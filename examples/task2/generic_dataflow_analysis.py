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
 

def generic_dataflow_solver(instructions, transfer_analysis, instruction_analysis, optimistic, merge, direction):        
    blocks, label_to_block = instruct_to_blocks(instructions)
    cfg = create_cfg(blocks, label_to_block)

    in_map = [{} for _ in range(len(blocks))]
    out_map = [{} for _ in range(len(blocks))]

    worklist = list(range(len(blocks)))

    if direction == "backward":
        input_feedback = out_map
        output_feedback = in_map
    else:
        input_feedback = in_map
        output_feedback = out_map

    while worklist:
        # pop either from bottom or top
        if direction == "backward":
            current = worklist.pop()
        else:
            current = worklist.pop(0)

        block = blocks[current]

        if direction == "backward":
            input = cfg[current]["successors"]
            output = cfg[current]["predecessors"]
        else:
            input = cfg[current]["predecessors"]
            output = cfg[current]["successors"]

        neighbors = [output_feedback[n] for n in input]
        # we merge in our neighbors facts
        merged_neighbors = merge(neighbors)
        input_feedback[current] = merged_neighbors

        # we then find the output feedback we are giving by performing our transfer analysis
        if optimistic: # if optimistic we don't do our instruction changes on the fly
            new_facts = transfer_analysis(input_feedback[current], block)
        else: # if pessimistic we perform our instruction changes on the fly
            new_facts = transfer_analysis(input_feedback[current], block)   
            blocks[current] = instruction_analysis(input_feedback[current], block)   

        # we check if the output feedback has changed and if so, we update the output
        if output_feedback[current] != new_facts:
            output_feedback[current] = new_facts
            worklist.extend(output)
    
    # if optimistic we perform our instruction changes at the end
    if optimistic:
        blocks  = instruction_analysis(input_feedback, blocks)
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
