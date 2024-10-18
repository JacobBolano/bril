import json
import sys
import logging
from copy import deepcopy
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

def add_pseudo_labels(blocks, label_to_block):
    current_pseudos = 0
    for i, block in enumerate(blocks):
        first_instruction = block[0]
        if "label" not in first_instruction:
            # we need to add a pseudo label
            label_to_add = {
                "label" : f"jacob_pseudo_label_{current_pseudos}"
            }
            label_to_block[label_to_add["label"]] = i
            block.insert(0, label_to_add)
            current_pseudos += 1
    return blocks, label_to_block

#ensures every cfg has single starting point
def add_entry_blocks(blocks, label_to_block):
    initial_label = blocks[0][0]["label"]

    incoming_edge_first_block = False
    for block in blocks:
        for instr in block:
            if "labels" in instr and initial_label in instr["labels"]:
                # we need to add an entry block
                incoming_edge_first_block = True
                break
    
    if incoming_edge_first_block:
        # fix label to block
        for block in blocks:
            block_label = block[0]["label"]
            label_to_block[block_label] += 1

        new_label = {
            "label" : "jacob_entry_label"
        }
        jmp_instr = {
            "op" : "jmp",
            "labels" : [initial_label]
        }
        new_block = [new_label, jmp_instr]
        blocks.insert(0, new_block)
        label_to_block[new_label["label"]] = 0
        return blocks, label_to_block
    else:
        return blocks, label_to_block

def create_cfg(blocks, label_to_block):
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

    return cfg

def find_dominators(blocks, cfg):
    # dom[b] = {b} U (all predecessors to b dom [p])
    dominators = {}
    for index, block in enumerate(blocks):
        dominators[index] = set(range(len(blocks)))
    # entry block only dominates itself
    dominators[0] = [0]

    converged = False
    while not converged:
        converged = True
        for i, block in enumerate(blocks):
            if i == 0: # we ignore the first block
                continue
            block_pred = cfg[i]["predecessors"]
            if block_pred:
                intersect_pred = set(dominators[block_pred[0]])
                # find intersection of predecessor dominators
                for p in block_pred[1:]:
                    intersect_pred &= set(dominators[p])
                new_dom = intersect_pred
                new_dom.add(i)
                if new_dom != dominators[i]:
                    # our dominators updated (reduced)
                    dominators[i] = new_dom
                    converged = False

    return dominators
    
def find_dom_front(blocks, cfg, dominators):
    
    dominance_frontier = {block_index: set() for block_index, block in enumerate(blocks)}
    # maps block_index: set of block indices in dominance frontier of block

    # JUST ADDED - NOW REMOVED
    block_indices = dominators.keys()
    strictly_dominators = {block_index: [] for block_index in block_indices} # maps block_index: the block_indices that strictly dominate it
    for block_b in block_indices:
        # find strictly dominators of block b
        for block_a in block_indices:
            if block_a == block_b:
                continue
            
            if block_a in dominators[block_b]:
                strictly_dominators[block_b].append(block_a)

    for i_a, block_a in enumerate(blocks):
        for i_b, block_b in enumerate(blocks):
            # if i_a == i_b:
            #      continue
            # check if A does not dominate B

            if i_a not in strictly_dominators[i_b]:
                # now check if A does dominate a predecessor of B

                pred_b = cfg[i_b]["predecessors"]
                # logging.debug(f"pred of {i_b} is {pred_b}")

                a_doms_b_pred = False
                for p_b in pred_b:
                    if i_a in dominators[p_b]:
                        a_doms_b_pred = True
                
                if a_doms_b_pred:
                    dominance_frontier[i_a].add(i_b)
    
    return dominance_frontier

def find_dom_tree(dominators):
    block_indices = dominators.keys()
    strictly_dominators = {block_index: [] for block_index in block_indices} # maps block_index: the block_indices that strictly dominate it
    dom_tree = {block_index: [] for block_index in block_indices} # maps block_index: the block_indices it immediately dominates

    for block_b in block_indices:
        # find strictly dominators of block b
        for block_a in block_indices:
            if block_a == block_b:
                continue
            
            if block_a in dominators[block_b]:
                strictly_dominators[block_b].append(block_a)
    
    # now we know strictly dominators, lets determine immediate ones
    for block in block_indices:
        strict_dom_blocks = strictly_dominators[block]
        for sd_b in strict_dom_blocks:
            immediately_dominates = True
            for other_sd_b in strict_dom_blocks:
                if sd_b == other_sd_b:
                    continue

                if sd_b in strictly_dominators[other_sd_b]: # our potential block sd another block that sds current block
                    immediately_dominates = False
                    break
            
            if immediately_dominates:
                dom_tree[sd_b].append(block)
    
    return dom_tree

def find_defs(blocks, variable):
    defs = set()
    for i, block in enumerate(blocks):
        for instr in block:
            if "dest" in instr:
                if instr["dest"] == variable:
                    defs.add(i)
    return defs

def find_all_defs(instructions, blocks):
    definitions = {} # maps variable: indices of blocks that define that variable
    for instr in instructions: # not sure about this logic and how it handles the same definition
        if "dest" in instr:
            if instr["dest"] not in definitions: # we only need to find the definitions once
                definitions[instr["dest"]] = find_defs(blocks, instr["dest"])

    return definitions

def insert_phi(var, type, block_index, phis):
    # this is all the phis for this block
    blocks_phis = phis[block_index]

    if var not in blocks_phis.keys():
        blocks_phis[var] = {
            "destination": "TRIVIAL",
            "type": type,
            "arguments": []
        }
    
    phis[block_index] = blocks_phis
    return phis


def convert_ssa(instructions, arguments):   
    arg_names = [argument["name"] for argument in arguments] if arguments else []
    blocks, label_to_block = instruct_to_blocks(instructions)
    # logging.debug(instructions)
    # we need to fix labels
    blocks, label_to_block = add_pseudo_labels(blocks, label_to_block)
    blocks, label_to_block = add_entry_blocks(blocks, label_to_block)
    # logging.debug(f"blocks {blocks}")
    # logging.debug(f"label to block {label_to_block}")
    cfg = create_cfg(blocks, label_to_block)
    # logging.debug(f"CFG {cfg}")
    dominators = find_dominators(blocks, cfg) # maps block_index: set of dominating blocks_indices
    #logging.debug(f"this is incorrect dominators at the start {dominators}")
    dominance_frontier = find_dom_front(blocks, cfg, dominators) # maps block_index: set of block indices in dominance frontier of block
    # logging.debug(f"this is incorrect dominance frontier {dominance_frontier}")
    dom_tree = find_dom_tree(dominators) # maps block_index: the block_indices it immediately dominates
    definitions = find_all_defs(instructions, blocks) # maps variable: indices of blocks that define that variable
    variables = definitions.keys() # all possible variables
    # logging.debug(f"i believe this is all the definitions: {definitions}")
    #phis = {block_index: {} for block_index, _ in enumerate(blocks)} # maps a block_index to a list of its phi functions (variable, type: list of (variable, source))
    phis = {block_index: {} for block_index, _ in enumerate(blocks)} 
    # maps a block_index to a list of its phi functions (variable: definition, type, args: list[variable, source]))

    # first insert trivial phis
    for instr in instructions:
        if "dest" in instr: # its a variable
            var = instr["dest"]
            converged = False
            while not converged:
                add_to_current_defs = deepcopy(definitions[var])
                converged = True
                for defining_block_index in definitions[var]:
                    # logging.debug(f"our dominance frontier at {defining_block_index} is {dominance_frontier[defining_block_index]}")
                    for block_index in dominance_frontier[defining_block_index]:
                        # logging.debug(f"defining blocks (Defs) {definitions[var]}")
                        # logging.debug(f"this is dominance frontier {dominance_frontier} when we insert phi at block index {block_index} for var {var}")
                        type = instr["type"]
                        phis = insert_phi(var, type, block_index, phis)
                        add_to_current_defs.add(block_index)

                if add_to_current_defs != definitions[var]:
                    definitions[var].update(add_to_current_defs)
                    converged = False
    # logging.debug(f"this is the dominators: {dominators}")
    # logging.debug(f"this is the dominance frontier {dominance_frontier}")            
    # logging.debug(f"this is phis after trivial {phis}")
    # rename variables
    stack_names = {var: [var] for var in variables} # maps variables to a stack of their names?
    var_to_count = {var: 0 for var in variables}

    def fresh_name(original_name):
        var_to_count[original_name] += 1
        var_num = var_to_count[original_name]
        new_name = f"{original_name}.{var_num}"
        return new_name
    
    def rename(block_index):
        block = blocks[block_index]
        old_stack = {k: list(v) for k, v in stack_names.items()}

        #update phi destination names
        if phis[block_index]:
            phis_list = phis[block_index]
            for original_var in phis_list.keys():
                fresh = fresh_name(original_var)
                values = phis_list[original_var]
                values["destination"] = fresh
                phis_list[original_var] = values
                stack_names[original_var].append(fresh)

        for instr in block:
            # logging.debug(f"looking at instruction {instr} and our stack is {stack_names}")
            # update args for normal instructions
            if "args" in instr and "op" in instr and instr["op"] != "jmp":
                new_args = [stack_names[arg][-1] if arg in stack_names else arg for arg in instr["args"]]
                instr["args"] = new_args
            # update args for branch instructions
            if "args" in instr and "op" in instr and instr["op"] == "br":
                updated_arguments = []
                for arg in instr["args"]:
                    if arg in stack_names:
                        # it exists so we should update the name
                        updated_arguments.append(stack_names[arg][-1])
                    else:
                        # keep the old
                        updated_arguments.append(arg)
                instr["args"] = updated_arguments
            # update destination of the instruction
            if "dest" in instr:
                # generate fresh name
                fresh = fresh_name(instr["dest"])
                stack_names[instr["dest"]].append(fresh)
                # logging.debug(f"just added {fresh} to stack {stack_names}")
                instr["dest"] = fresh
        for succ in cfg[block_index]["successors"]:
            succs = cfg[block_index]["successors"]
            to_remove = []
            for original_var in phis[succ].keys():
                phi_function = phis[succ][original_var]
                #var_dest = phi_function["destination"] if phi_function["destination"] != "TRIVIAL" else original_var
                phi_function_arguments = phi_function["arguments"]
                # update the arg in this phi corresponding to block to stack[v].top
                # logging.debug(f"Looking at phi function {phi_function} with original var {original_var}")
                # logging.debug(f"but also stack is {stack_names}")
                # logging.debug(f" and our block is {block}")
                # logging.debug(f" and our successors at this block is {succs}")

                # we never defined in this block
                if len(stack_names[original_var]) <= 1:
                    # but this is one of our arguments to the method
                    if original_var in arg_names:
                        argument_name = original_var
                    else:
                        argument_name = "__undefined"
                else:
                    argument_name = stack_names[original_var][-1]
                arguments_label = block[0]['label']
                phi_function_arguments.append((argument_name, arguments_label))
            # for removal in to_remove:
            #     del phis[succ][removal]
        # rename child in dominator tree
        for child in dom_tree[block_index]:
            rename(child)

        #     restore the stack by popping what we pushed
        stack_names.clear()
        stack_names.update(old_stack)

    # we call rename on the first block which calls subsequent blocks
    rename(0)
    # we then fix blocks ot actually insert the phis
    # logging.debug(f"phis {phis}")
    for block_index in phis:
        list_phi_functions = phis[block_index]
        for original_variable in list_phi_functions:
            phi_function = list_phi_functions[original_variable]
            formatted_instruction = {
                "dest": phi_function["destination"],
                "type": phi_function["type"],
                "op": "phi",
                "args": [argument[0] for argument in phi_function["arguments"]],
                "labels": [argument[1] for argument in phi_function["arguments"]]
            }
            blocks[block_index].insert(1, formatted_instruction)
    # then we rebuild our instruction list with new blocks
    return rebuild_instructions(blocks)


def rebuild_instructions(blocks):
    output = []
    for block in blocks:
        for instr in block:
            output.append(instr)
    return output
                    
if __name__ == "__main__":
    prog = json.load(sys.stdin)

    for fn in prog["functions"]:
        fn["instrs"] = convert_ssa(fn["instrs"], fn["args"] if "args" in fn else None) 
    json.dump(prog, sys.stdout, indent=2)
