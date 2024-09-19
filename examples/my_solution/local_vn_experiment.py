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
    elif op == "not":
        return not args[0]
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
            for index, arg in enumerate(inst.get("args", [])):
                if arg in var_2_vNum:
                    arguments_vNum = var_2_vNum[arg]
                    arguments_value = vNum_2_val[arguments_vNum]
                    logging.debug(arguments_value)
                    if arguments_value[0] == "const":
                        # we can do constant propogation
                        args.append(arguments_value[1])
                        inst["args"][index] = int(arguments_value[1])
                    else:
                        args.append(var_2_vNum[arg])
                else:
                    args.append(arg)
            logging.debug(args)

            allInts = True
            for arg in args:
                if not isinstance(arg, int):
                    allInts = False
            
            if allInts:
                output = constant_folder(inst.get('op'), args)
                if output:
                    # we now have a constant value that we got from doing the folding
                    inst["op"] = "const"
                    inst["value"] = output
                    inst["args"] = []
                    # we can update our tables without worrying about collisions
                    value = (inst.get('op'), inst.get('value'))
                    vNum = index
                    val_2_vNum[value] = vNum
                    vNum_2_val[vNum] = value
                    var_2_vNum[inst["dest"]] = vNum
                    vNum_2_var[vNum] = inst["dest"]
                    index += 1
                    # move to the next instruction
                    continue

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
