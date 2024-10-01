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
        vNum_2_val = {}
        var_2_vNum = {} # variables --> value number
        vNum_2_var = {} # value number --> variables
        index = 0

        for inst in block:
            # canonicalize the instruction's arguments by getting the 
            # value numbers currently held by those vars
            args = []
            for arg in inst.get("args", []):
                if arg in var_2_vNum:
                    args.append(var_2_vNum[arg])
                else:
                    args.append(arg)

            # logging.debug(f"Looking at instruction: {inst}")
            # logging.debug(f"val_2_VNum is currently: {val_2_vNum}")
            # logging.debug(f"var_2_vNum is currently: {var_2_vNum}")
            # logging.debug(f"vNum_2_var is currently: {vNum_2_var}")
            commutative = {"add", "mul", "and", "or", "xor"}
            # create a new value by packaging this instruction with the value numbers of its arguments
            # if we are dealing with consts, the way we save this is unique
            if inst.get("op") == "const":
                value = (inst.get('op'), inst.get('value'))
            elif inst.get("op") in commutative:
                # the order does not matter so we sort to find instructions that are the same, but different ordering
                value = (inst.get("op"),) + tuple(sorted(args))
            else:
                value = (inst.get("op"),) + tuple(args)

            # look up the value number of this value
            vNum = val_2_vNum.get(value)

            if vNum is None:
                # we've never seen this value before, so lets create a new index and add it
                vNum = index
                val_2_vNum[value] = vNum
                vNum_2_val[vNum] = value
                index += 1
            else:
                # we've seen this value before
                # replace this instruction with an id and the arguments of the one we seen before
                # logging.error(f"We saw Value number {vNum} before for instruction {inst}")
                # logging.error(f"Our vnum2var map is {vNum_2_var}")
                inst["op"] = "id"
                inst["args"] = [vNum_2_var[vNum][0]]

            if "dest" in inst:
                # check we have a destination
                if inst.get("dest") in var_2_vNum:
                    # if dest is already in var_2_vNum, let's delete it 
                    previous_vNum = var_2_vNum[inst["dest"]]

                    if len(vNum_2_var[previous_vNum]) == 1:
                        # this is the last instruction to have that value, we also remove it from val2Vnum
                        old_value = vNum_2_val[previous_vNum]
                        del val_2_vNum[old_value]
                        del vNum_2_val[previous_vNum]
                    # remove the previous instruction from our value number - variable lists
                    vNum_2_var[previous_vNum].remove(inst["dest"])
                    del var_2_vNum[inst["dest"]]

                # update the variable at dest to point to our valNum
                var_2_vNum[inst["dest"]] = vNum
                # check whether we need to create a new list or append to the current
                if vNum in vNum_2_var:
                    vNum_2_var[vNum].append(inst["dest"])
                else:
                    vNum_2_var[vNum] = [inst["dest"]]

    return instructions

if __name__ == "__main__":
    prog = json.load(sys.stdin)

    for fn in prog["functions"]:
        fn["instrs"] = lvn(fn["instrs"]) 
    json.dump(prog, sys.stdout, indent=2)
