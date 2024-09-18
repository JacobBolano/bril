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

def dead_code_eliminator(instructions):

    blocks = instruct_to_blocks(instructions)

    updated_instructions = []

    for block in blocks:
        # iterate until convergence
        converged = False
        while not converged:
            # find unused variables in this block
            unused = {}
            instructions_to_remove = set()

            for index, instruction in enumerate(block):
                
                # look at instructions that use other variables. delete that from unused if they exist
                #logging.debug("unused state: " + str(unused))
                args = instruction.get("args", [])
                for arg in args:
                    if arg in unused:
                        del unused[arg]

                dest = instruction.get("dest")
                logging.debug("dest: " + str(dest))

                if dest:
                    # if our variable was previously marked unused, it is used so remove
                    logging.debug("unused current state: " + str(unused))
                    if dest in unused:
                        instructions_to_remove.add(unused[dest])
                        logging.debug("unused to remove " + str(unused[dest]))
                    # update unused to current instruction
                    unused[dest] = index
            
            #logging.debug(instructions_to_remove)

            new_block = []
            for index, instruction in enumerate(block):
                if index not in instructions_to_remove:
                    new_block.append(instruction)
            # update current block to the new block we made
            block = new_block
            if not instructions_to_remove:
                converged = True
        # we converged
        updated_instructions += [instruction for instruction in block]
    return updated_instructions


if __name__ == "__main__":
    prog = json.load(sys.stdin)
    #logging.info(sys.stdin)
    for fn in prog["functions"]:
        fn["instrs"] = dead_code_eliminator(fn["instrs"]) 
    json.dump(prog, sys.stdout, indent=2)
