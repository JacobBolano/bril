import json
import sys
import logging

#logging.basicConfig(filename='debug.log', level=logging.DEBUG)


def is_pure(instr):
    return instr.get("op") in {"add", "mul", "sub", "div", "and", "or", "xor"}

def dead_code_eliminator(instructions):

    # our code is "dead code" if it is pure or its result is never used.
    used = set()

    for instr in instructions:
        used.update(instr.get("args", []))    

    #logging.debug(used)


    alive_code = [] 
    for instr in instructions:
        if instr.get("dest") in used or not is_pure(instr):
            alive_code.append(instr)
            used.update(instr.get("args", []))

    
    return alive_code


if __name__ == "__main__":
    prog = json.load(sys.stdin)
    #logging.info(sys.stdin)
    for fn in prog["functions"]:
        fn["instrs"] = dead_code_eliminator(fn["instrs"]) 
    json.dump(prog, sys.stdout, indent=2)
