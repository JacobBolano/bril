import json
import sys
import logging

#logging.basicConfig(filename='debug.log', level=logging.DEBUG)

def dead_code_eliminator(instructions):

    # our code is "dead code" if it is pure or its result is never used.
    converged = False
    while not converged:
        # each time we look at what variables are actually used
        used = set()

        for instr in instructions:
            used.update(instr.get("args", []))    
        #logging.debug(used)

        # the actual instructions that we want to add this pass
        updated_instructions = []
        for instr in instructions:

            #logging.debug("we are looking at " + str(instr))
            # first check if this is a print style instruction
            if "dest" not in instr:
                updated_instructions.append(instr)
            else:
                # then check if we actually use the destination
                if instr.get("dest") in used:
                    updated_instructions.append(instr)
        if updated_instructions == instructions:
            # we didn't change anything
            converged = True
        else:
            instructions = updated_instructions
    
    return instructions


if __name__ == "__main__":
    prog = json.load(sys.stdin)
    #logging.info(sys.stdin)
    for fn in prog["functions"]:
        fn["instrs"] = dead_code_eliminator(fn["instrs"]) 
    json.dump(prog, sys.stdout, indent=2)
