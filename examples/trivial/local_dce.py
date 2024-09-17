import json
import sys
import logging

#logging.basicConfig(filename='debug.log', level=logging.DEBUG)

def check_pure(instr):
    return instr.get("op") in {"add", "mul", "sub", "div", "const"}


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

def dead_code_eliminator(instructions):

    blocks = instruct_to_blocks(instructions)
    # our code is "dead code" if it is pure or its result is never used.
    used = set()
    unused = {}
    for block in blocks:
        for inst in block:
            args = inst.get("args", [])
            for arg in args:
                used.add(arg)

    alive_code = []

    for block in blocks:
        for instruction in block:
            dest = instruction.get("dest")
            if dest in used or not check_pure(instruction):
                alive_code.append(instruction)
            elif dest:
                unused[dest] = instruction
    
    return alive_code


if __name__ == "__main__":
    prog = json.load(sys.stdin)
    #logging.info(sys.stdin)
    for fn in prog["functions"]:
        fn["instrs"] = dead_code_eliminator(fn["instrs"]) 
    json.dump(prog, sys.stdout, indent=2)
