import json
import sys
import copy
import logging
from collections import defaultdict
from generic_dataflow_analysis import generic_dataflow_solver
from const_prop import constant_folder

def liveness_transfer(out_map_current, block):
    new_facts = copy.deepcopy(out_map_current)

    for instr in reversed(block):
        # Remove kill(b) from our facts
        if "dest" in instr:
            dest = instr["dest"]
            new_facts.pop(dest, None)

        if "args" in instr:
            args = instr["args"]
            for arg in args:
                new_facts[arg] = True
    
    return new_facts

def liveness_instruction_analysis(output_feedback, blocks):
    out_map = output_feedback
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
                current_outs.pop(dest, None)

            if "args" in instr:
                args = instr["args"]
                for arg in args:
                    current_outs[arg] = True
        
        updated_blocks.append(updated_block)
    return updated_blocks

def liveness_merge(successor_facts):
    output = {}

    for fact in successor_facts:
        # version of union using dicitonaries
        for key in fact:
            if key not in output:
                output[key] = True
    return output

def const_transfer(in_map_current, block):
    # only update our map
    new_facts = copy.deepcopy(in_map_current) if in_map_current else {}
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
                else:
                    new_facts[instr["dest"]] = '?'
            else:
                # we don't know what it is
                new_facts[instr["dest"]] = '?'

    return new_facts

def const_instruction_analysis(in_map_current, block):
    
    new_facts = copy.deepcopy(in_map_current) if in_map_current else {}
    # logging.debug(f"new facts: {new_facts}")
    for i, instr in enumerate(block):
        if "dest" in instr:
            if instr["op"] in {"add", "sub", "mul", "div", "and", "not", "eq", "lt", "gt", "le", "ge"}:
                # check that these arguments exist in new_facts and then check that they are real (not ?)
                if all(arg in new_facts for arg in instr['args']) and all(new_facts[arg] != '?' for arg in instr['args']):
                    constant_fold_result = constant_folder(instr["op"], [new_facts[x] for x in instr["args"]])
                    # create new instruction
                    new_instruction = {}
                    new_instruction["op"] = "const"
                    new_instruction["type"] = instr["type"]
                    new_instruction["value"] = constant_fold_result
                    new_instruction["dest"] = instr["dest"]

                    #update block
                    block[i] = new_instruction
            elif instr["op"] in {"not", "id"}:
                if instr['args'][0] in new_facts and new_facts[instr['args'][0]] != '?':
                    # check that these argument exists in new_facts and then check that it is real (not ?)
                    copied_value = new_facts[instr["args"][0]]
                    if instr['op'] == 'not':
                        copied_value = not copied_value
                    # create new instruction
                    new_instruction = {}
                    new_instruction["op"] = "const"
                    new_instruction["type"] = instr["type"]
                    new_instruction["value"] = copied_value
                    new_instruction["dest"] = instr["dest"]
                    
                    #update block
                    block[i] = new_instruction
    return block

def const_merge(predecessor_facts):
    # merge facts
    if not predecessor_facts:
        return {}
    # check if any of the predecessor facts are empty
    if any(d == {} for d in predecessor_facts):
        return {}
    
    output = {}

    for fact in predecessor_facts:
        for key, value in fact.items():
            if value == '?':
                output[key] = '?'
            else:
                # if we already saw this key before
                if key in output:
                    # if the values are different, this variable is no longer constant
                    if output[key] != value:
                        output[key] = '?'
                    # otherwise we keep it
                else:
                    # add to the map
                    output[key] = value
    return output


# Example usage:
if __name__ == "__main__":
    prog = json.load(sys.stdin)
    for fn in prog["functions"]:
        # example for liveness
        optimistic = True
        direction = "backward"
        fn["instrs"] = generic_dataflow_solver(fn["instrs"], liveness_transfer, liveness_instruction_analysis, 
                                               optimistic, liveness_merge, direction) 
        # example for const_prop
        # direction = "forward"
        # optimistic = False
        # fn["instrs"] = generic_dataflow_solver(fn["instrs"], const_transfer, const_instruction_analysis, 
        #                                        optimistic, const_merge, direction) 
    json.dump(prog, sys.stdout, indent=2)