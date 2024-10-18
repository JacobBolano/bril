import json
import sys
import logging
from copy import deepcopy
from collections import defaultdict
from convert_ssa import instruct_to_blocks, add_entry_blocks, add_pseudo_labels, create_cfg, find_dominators

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
        # pre header
        loops[f"loop{num_loops}"] = {
            "loop_components": natural_loop,
            "header" : begin_loop,
            "preheader" : None,
            "latch" : None,
            "exits" : None
        }
        num_loops += 1
    return loops


def find_licm(instructions):
    blocks, label_to_block = instruct_to_blocks(instructions)
    blocks, label_to_block = add_pseudo_labels(blocks, label_to_block)
    blocks, label_to_block = add_entry_blocks(blocks, label_to_block)
    cfg = create_cfg(blocks, label_to_block)
    dominators = find_dominators(blocks, cfg) # maps block_index: set of dominating blocks_indices
    back_edges = find_back_edges(dominators, blocks, cfg)
    loops = find_loops(back_edges, cfg)
    logging.debug(f"back edges {back_edges}")
    logging.debug(f"loops {loops}")
    pass

if __name__ == "__main__":
    prog = json.load(sys.stdin)

    for fn in prog["functions"]:
        fn["instrs"] = find_licm(fn["instrs"]) 
    json.dump(prog, sys.stdout, indent=2)