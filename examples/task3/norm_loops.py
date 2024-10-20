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
        # NOTE: normalizing loops while finding them messes up the indices of these loops. I should separate this work

       
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

def fix_loops(index_changed, loops):
    new_loops = {}

    for loop_key in loops:
        loop = loops[loop_key]
        loop_components = loop["loop_components"]
        header = loop["header"]
        preheader = loop["preheader"]
        latch = loop["latch"]
        start = header if preheader == "TRIVIAL" else preheader

        if start <= index_changed <= latch:
            logging.debug(f" had to update loop due to index in betweeen")
            # our index changed is in betweeen - its part of this loop
            # this means our latch increased by 1 and our total components did as well
            latch += 1
            loop_components.append(latch)
            # we check if its at header or preheader - this shouldnt happen
            if index_changed == header:
                logging.debug(f"this shouldnt happen")
                header += 1
            if preheader != "TRIVIAL" and index_changed == preheader:
                logging.debug(f"this shouldnt happen")
                preheader += 1
        elif start > index_changed:
            logging.debug(f" had to update loop due to index before")
            # index changed is before our loop - we must shift everything in the loop
            loop_components = [loop_component + 1 for loop_component in loop_components] # first update loop components
            header += 1
            if preheader != "TRIVIAL":
                preheader += 1
            latch += 1
        
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
    loop_keys = loops.keys()
    for loop_key in loop_keys:
        curr_loop = loops[loop_key]
        cur_loop_header = curr_loop["header"]

        # pre header potentials are a predecessor but they are also earlier than the header block
        preds_header = [preds for preds in cfg[cur_loop_header]["predecessors"] if preds < cur_loop_header]
        #logging.debug(f"these are potential preheaders {preds_header}")
        if len(preds_header) != 1:
            # there is more than one predecessor to a header
            # we need to insert a preheader
            pre_header = []
            pre_header.append({
                'label' : f'jacob_preheader_{curr_pseudos}'
            })
            curr_pseudos += 1
            pre_header.append({
                "op": "jmp",
                "labels" : [blocks[cur_loop_header][0]["label"]]
            })
            # update blocks, cfg, label to block, loops
            index_pre_header = cur_loop_header
            blocks.insert(cur_loop_header, pre_header) # update blocks, shifts indices after pre header by 1
            label_to_block = fix_labels(index_pre_header, label_to_block) # shift label to blocks
            label_to_block[pre_header[0]['label']] = index_pre_header # update map that goes from labels to block index

            # logging.debug(f"this is our blocks before recreating cfg {blocks}")
            # logging.debug(f"this is our label to block before recreating cfg {label_to_block}")
          
            cfg = create_cfg(blocks, label_to_block) # update our cfg based on new blocks and label to block 
            #logging.debug(f"Inserted a pre header {pre_header}")

            # update loops
            loops = fix_loops(index_pre_header, loops)
        else:
            index_pre_header = preds_header[0]
        
        # add pre header
        if curr_loop["preheader"] == "TRIVIAL":
            curr_loop["preheader"] = index_pre_header
    
    return loops, blocks, label_to_block
        
def perform_licm(normalized_loops, blocks):

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
        instructions_to_hoist = []
        for block in loop_components:
            for instruction in blocks[block]:
                # check deterministic
                if "op" in instruction and instruction["op"] in {"load", "store", "store", "free", "ptradd"}:
                    continue
                # check arguments are loop invariant
                if "args" in instruction and any(arg in vars_defined_in_loop for arg in instruction["args"]):
                    continue
                
                # this instruction is loop invariant 
                instructions_to_hoist.append((instruction, block))
        
        for instruction in instructions_to_hoist:
            # first add it to preheader
            blocks[preheader].append(instructions_to_hoist[0])
            # next remove from original block in loop
            blocks[instructions_to_hoist[1]].remove(instructions_to_hoist[0])
    
    return blocks


        



def find_licm(instructions):
    blocks, label_to_block = instruct_to_blocks(instructions) # convert instructions to blocks
    blocks, label_to_block = add_pseudo_labels(blocks, label_to_block) # add any pseudo labels for unlabeled code
    blocks, label_to_block = add_entry_blocks(blocks, label_to_block) # add an entry block if not already there
    cfg = create_cfg(blocks, label_to_block) # create our CFG
    #logging.debug(f"initial cfg {cfg}")
    dominators = find_dominators(blocks, cfg) # maps block_index: set of dominating blocks_indices
    back_edges = find_back_edges(dominators, blocks, cfg) # find back enges
    #logging.debug(f"back edges {back_edges}")
    loops = find_loops(back_edges, cfg) # find loops
    #logging.debug(f"loops found {loops}")
    normalized_loops, blocks, label_to_block = normalize_loops(loops, blocks, label_to_block, cfg) # normalize loops
    #logging.debug(f"blocks updated after normalizing {blocks}")
    #logging.debug(f"cfg updated after loops normalized: {cfg}")
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