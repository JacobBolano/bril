import json
import sys
import logging
from copy import deepcopy
from collections import defaultdict
from convert_ssa import instruct_to_blocks, add_entry_blocks, add_pseudo_labels, create_cfg, find_dominators, rebuild_instructions

logging.basicConfig(filename='debug.log', level=logging.DEBUG)

def find_back_edges(dominators, blocks, cfg):
    back_edges = [] # contains list of our back edges where 0: end_edge and 1: start_edge
    for i_a, block_a in enumerate(blocks):
        blocks_succ = cfg[i_a]["successors"]
        for succ_b in blocks_succ:
            if succ_b in dominators[i_a]:
                back_edges.append([i_a, succ_b])
    
    return back_edges

def find_loops(back_edges, cfg):
    loops = {} # maps from a unique loop name to the loop_components, header, preheader, latch, exits
    num_loops = 0
    for back_edge in back_edges:
        begin_loop = back_edge[1] # header
        end_loop = back_edge[0] # node that points to header
        natural_loop = [begin_loop]

        visited = set()
        nodes_to_explore = [end_loop]

        while nodes_to_explore:
            current_node = nodes_to_explore.pop()
            if current_node in visited or current_node == begin_loop:
                # we already visited or its the header which we ignore
                continue
            visited.add(current_node)
            # we then need to check the predecessors of current node (working backwards)
            for pred in cfg[current_node]["predecessors"]:
                nodes_to_explore.append(pred)
        natural_loop.extend(visited)

       
        loops[f"loop{num_loops}"] = {
            "loop_components": natural_loop,
            "header" : begin_loop,
            "preheader" : "TRIVIAL",
            "latch" : end_loop,
            "exits" : "TRIVIAL"
        }
        num_loops += 1
    return loops

def fix_labels(index_changed, label_to_block):
    # update blocks after index
    for label in label_to_block:
        if label_to_block[label] >= index_changed:
            # this is every block after or equal to the index we shifted
            label_to_block[label] += 1
    return label_to_block

def fix_loops(index_changed, loops, loop_key_changed):
    new_loops = {}

    for loop_key in loops:
        loop = loops[loop_key]
        if loop_key == loop_key_changed:
            new_loops[loop_key] = {
                "loop_components" : loop["loop_components"],
                "header" : loop["header"],
                "preheader" : loop["preheader"],
                "latch" : loop["latch"],
                "exits" : "TRIVIAL"
            }
            continue
        loop_components = []
        for lcp in loop["loop_components"]:
            if lcp >= index_changed:
                loop_components.append(lcp +1)
            else:
                loop_components.append(lcp)
        header = loop["header"]
        header = header if header < index_changed else header + 1
        preheader = loop["preheader"]
        if preheader != "TRIVIAL":
            if preheader >= index_changed:
                preheader += 1
        latch = loop["latch"]
        latch = latch if latch < index_changed else latch + 1
        
        # update loops (Add to new loops)
        new_loops[loop_key] = {
            "loop_components": loop_components,
            "header" : header,
            "preheader" : preheader,
            "latch" : latch,
            "exits" : "TRIVIAL"
        }
    return new_loops        
            
def normalize_loops(loops, blocks, label_to_block, cfg):
    curr_pseudos = 0
    loop_keys = list(loops.keys())
    for loop_key in loop_keys:
        curr_loop = loops[loop_key]
        cur_loop_header = curr_loop["header"]

        # pre header potentials are a predecessor but they cant be in a loop where the header is current header
        all_loops = set()
        for lp_key in loop_keys:
            if loops[lp_key]["header"] == cur_loop_header:
                all_loops.update(loops[lp_key]["loop_components"])

        preds_header = [preds for preds in cfg[cur_loop_header]["predecessors"] if preds not in all_loops]


        if len(preds_header) != 1:
            # there is more than one predecessor to a header
            # we need to insert a preheader
            pre_header = []
            curr_loop_header_label = blocks[cur_loop_header][0]["label"]
            pre_header.append({
                'label' : f'jacob_preheader_{curr_pseudos}'
            })
            curr_pseudos += 1
            pre_header.append({
                "op": "jmp",
                "labels" : [curr_loop_header_label]
            })
            # update blocks, cfg, label to block, loops
            index_pre_header = cur_loop_header
            blocks.insert(cur_loop_header, pre_header) # update blocks, shifts indices after pre header by 1
            label_to_block = fix_labels(index_pre_header, label_to_block) # shift label to blocks
            label_to_block[pre_header[0]['label']] = index_pre_header # update map that goes from labels to block index

            # update current loop components because they are now shifted
            curr_loop["loop_components"] = [cp + 1 if cp >= index_pre_header else cp for cp in curr_loop["loop_components"]]
            curr_loop["header"] += 1
            curr_loop["latch"] = curr_loop["latch"] + 1 if curr_loop["latch"] >= index_pre_header else curr_loop["latch"]

            # we need to fix the control flow. predecessor blocks earlier than our header now point to preheader.
            preds_header = [pd if pd < index_pre_header else pd + 1 for pd in preds_header]
            for pred in preds_header:
                pred_block = blocks[pred]
                if "preheader" in pred_block[0]["label"]:
                    continue # this is a preheader so dont change the logic
                last_instruction = pred_block[-1]
                if "op" in last_instruction:
                    if last_instruction["op"] == "jmp":
                        last_instruction["labels"] = [pre_header[0]["label"]]
                    elif last_instruction["op"] == "br":
                        labels = []
                        for label in last_instruction["labels"]:
                            if label == curr_loop_header_label: # the label in the branch was previously our header
                                labels.append(pre_header[0]["label"])
                            else:
                                labels.append(label)
                        last_instruction["labels"] = labels
                blocks[pred][-1] = last_instruction
                # if there is no op or its not a jump style instruciton, then it will "fall" to the preheader naturally
            cfg = create_cfg(blocks, label_to_block) # update our cfg based on new blocks and label to block 

            # update phis if they now are different predecessor
            for instr in blocks[curr_loop["header"]]:
                if "op" in instr and instr["op"] == "phi": # check if its a phi
                    # we check the labels of this phi function and see if they now go through the preheader
                    new_labels = []
                    for label in instr["labels"]:
                        phi_label_block = label_to_block[label]
                        if phi_label_block in preds_header and "preheader" not in label: # this block label was a previous predecessor to header
                            # this meanas it now flows through our preheader
                            new_labels.append(pre_header[0]["label"])
                        else: # this was not a predecessor, label it normally
                            new_labels.append(label)
                    instr["labels"] = new_labels

            # update other loops
            loops = fix_loops(index_pre_header, loops, loop_key)
        else:
            index_pre_header = preds_header[0]
        
        # add pre header
        curr_loop["preheader"] = index_pre_header
        loops[loop_key] = curr_loop
    return loops, blocks, label_to_block

def perform_licm(normalized_loops, blocks):

    safe_to_hoist = {} # maps instruction to the (loop, block) its in

    for loop_key in normalized_loops:
        loop = normalized_loops[loop_key]
        loop_components = loop["loop_components"]
        header = loop["header"]
        preheader = loop["preheader"]
        latch = loop["latch"]

        # first we find the set of variables defined in the loop
        vars_defined_in_loop = set()
        for block in loop_components:
            for instruction in blocks[block]:
                if "dest" in instruction:
                    vars_defined_in_loop.add(instruction["dest"])
        
        # then we check each instruction and see if it is deterministic and if all arguments are defined outside the loop
        for block in loop_components:
            for instruction in blocks[block]:
                # instruction_tuple = make_instruction_hashable(instruction)
                if "dest" in instruction:
                    var = instruction["dest"]
                    # check deterministic
                    if "op" in instruction and instruction["op"] in {"call", "load", "store", "free", "ptradd", "jmp", "br", "ret", "phi"}:
                        if var in safe_to_hoist:
                            # we need to delete it as its no longer safe
                            del safe_to_hoist[var]
                        continue
                    if "op" in instruction and instruction["op"] == "id" and instruction["type"] == {'ptr': 'int'}:
                        if var in safe_to_hoist:
                            # we need to delete it as its no longer safe
                            del safe_to_hoist[var]
                        continue
                    if "label" in instruction:
                        # if instruction_tuple in safe_to_hoist:
                        if var in safe_to_hoist:
                            # we need to delete it as its no longer safe
                            del safe_to_hoist[var]
                        continue
                    # check arguments are loop invariant
                    if "args" in instruction and any(arg in vars_defined_in_loop for arg in instruction["args"]):
                        # if instruction_tuple in safe_to_hoist:
                        if var in safe_to_hoist:
                            # we need to delete it as its no longer safe
                            del safe_to_hoist[var]
                        continue
                    
                    # this instruction is loop invariant 
                    safe_to_hoist[var] = (loop_key, block, instruction)
        

    for var in safe_to_hoist:
        instruction_tuple = safe_to_hoist[var]
        loop_key = instruction_tuple[0]
        block = instruction_tuple[1]
        instruction = instruction_tuple[2]

        loop = normalized_loops[loop_key]
        preheader = loop["preheader"]
        # first add it to preheader
        # check if last instruction is a jmp style instruction
        last_instruction = blocks[preheader][-1]
        if "op" in last_instruction and (last_instruction["op"] == "jmp" or last_instruction["op"] == "br"):
            # then we need to insert before this jmp
            blocks[preheader].insert(len(blocks[preheader]) - 1, instruction)
        else:
            blocks[preheader].append(instruction)
        # next remove from original block in loop
        blocks[block].remove(instruction)

    return blocks


def find_licm(instructions):
    blocks, label_to_block = instruct_to_blocks(instructions) # convert instructions to blocks
    # below code already done in ssa
    # blocks, label_to_block = add_pseudo_labels(blocks, label_to_block) # add any pseudo labels for unlabeled code
    # blocks, label_to_block = add_entry_blocks(blocks, label_to_block) # add an entry block if not already there
    cfg = create_cfg(blocks, label_to_block) # create our CFG
    dominators = find_dominators(blocks, cfg) # maps block_index: set of dominating blocks_indices
    back_edges = find_back_edges(dominators, blocks, cfg) # find back edges

    loops = find_loops(back_edges, cfg) # find loops    

    normalized_loops, blocks, label_to_block = normalize_loops(loops, blocks, label_to_block, cfg) # normalize loops
    # NOTE: if we want just normalized loops we return now
    # return rebuild_instructions(blocks)
    # NOTE: otherwise we find licm and move them   
    blocks = perform_licm(normalized_loops, blocks)
    return rebuild_instructions(blocks)

if __name__ == "__main__":
    prog = json.load(sys.stdin)

    for fn in prog["functions"]:
        fn["instrs"] = find_licm(fn["instrs"]) 
    json.dump(prog, sys.stdout, indent=2)