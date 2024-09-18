#You must implement LVN that performs common subexpression elimination.
# You may (but don't have to) implement some of the extensions discussed above (folding, commutativity, etc.).
# You may choose how to handle "clobbered" variables. Just be sure to document your choice.

import json
import sys
import logging

logging.basicConfig(filename='debug.log', level=logging.DEBUG)

def check_jump(instr):
    return instr.get("op") in {"jmp", "br", "ret"}

def instruct_to_blocks(instructions):
    blocks = []
    current_block = []
    
    for instruction in instructions:

        if "op" in instruction:
            current_block.append(instruction)
            
            if check_jump(instruction):
                blocks.append(current_block)
                current_block = []
        else:

            if current_block:
                blocks.append(current_block)

            current_block = [instruction]

    if current_block:
        blocks.append(current_block)
    
    return blocks


def lvn(instructions):
    
    blocks = instruct_to_blocks(instructions)
    for block in blocks:

        val_2_vNum  = {} # the value we create --> value number
        var_2_vNum = {} # variables --> value number
        vNum_2_var = {} # value number --> variables
        index = 0

        for inst in block:
            # canonicalize the instruction's arguments by getting the 
            # value numbers currently held by those vars
            args = [var_2_vNum[arg] for arg in inst.get("args", []) if arg in var_2_vNum]

            # create a new value by packaging this instruction with the value numbers of its arguments
            # if we are dealing with consts, the way we save this is unique
            if inst.get("op") == "const":
                value = (inst.get('op'), inst.get('value'))
            else:
                value = (inst.get("op"),) + tuple(args)
            logging.debug(value)

            # look up the value number of this value
            vNum = val_2_vNum.get(value)

            if vNum is None:
                # we've never seen this value before, so lets create a new index and add it
                vNum = index
                val_2_vNum[value] = vNum
                index += 1
            else:
                # we've seen this value before
                # replace this instruction with an id and the arguments of the one we seen before
                inst["op"] = "id"
                inst["args"] = [vNum_2_var[vNum]]

            if "dest" in inst:
                # check we have a destination
                if inst.get("dest") in var_2_vNum:
                    # if dest is already in vNum_2_var, let's delete it 
                    temp = var_2_vNum[inst.get("dest")]
                    if temp in vNum_2_var:
                        del vNum_2_var[temp]

                # update the variable at dest to point to our valNum
                var_2_vNum[inst["dest"]] = vNum
                vNum_2_var[vNum] = inst["dest"]

    return instructions

if __name__ == "__main__":
    prog = json.load(sys.stdin)

    for fn in prog["functions"]:
        fn["instrs"] = lvn(fn["instrs"]) 
    json.dump(prog, sys.stdout, indent=2)
