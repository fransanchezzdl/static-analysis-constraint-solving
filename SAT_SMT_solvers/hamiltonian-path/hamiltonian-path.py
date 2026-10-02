# Francisco José Sánchez de León Acevedo
# Assignment 1: Hamiltonian paths

# This file generates an SMT-LIB2 script for the hamiltonian path assignment1 problem

from z3 import *

# Class to store and manage graphs

class Graph:
  def __init__(self, vertices, edges):
    self.vertices = set(vertices)
    self.adj_list = { v: set() for v in vertices }
    
    for (x, y) in edges:
      self.add_edge(x, y)

  def add_edge(self, v1, v2):
    self.adj_list[v1].add(v2)
    self.adj_list[v2].add(v1)
      
  def get_vertices(self):
    return self.vertices
    
  def get_adjacents(self, vertex):
    return self.adj_list[vertex]
  

# The following function determines whether the graph given
# can be coloured with k colours.

def has_hamiltonian_path(graph):
    vertices = list(graph.get_vertices())
    n = len(vertices)

    # For each pair (vertex, position), generate a Z3
    # Boolean constant whose name is p_vertex_position.
    #
    # Positions are numbered from 1 to n.
    prop_vars = {
        v: [Bool("p_%d_%d" % (v, pos)) for pos in range(1, n+1)] for v in vertices
    }

    solver = Solver()

    # Constraint 1:
    #
    # Every vertex must appear in the sequence.
    #
    # For every vertex v:
    #
    # p_v_1 OR p_v_2 OR ... OR p_v_n

    for v in vertices:
        solver.append(
        Or([prop_vars[v][pos - 1] for pos in range(1, n+1)])
        )

    # Constraint 2:
    #
    # Every vertex must NOT appear more than once in the sequence.
    #
    # For every vertex v and two different positions within 1 to n:
    #
    # NOT (p_v_position1 AND p_v_position2), equivalent to p_v_position1 -> NOT p_v_position2
    #
    # This means that if vertex v occurs in one position, it doesn't occur in other.

    for v in vertices:
        for position1 in range(1, n+1):
            for position2 in range(1, n+1):
                if position1 != position2:
                    solver.append(Implies(
                        prop_vars[v][position1 - 1],
                        And([Not(prop_vars[v][position2 - 1])])
                    ))

    # Constraint 3:
    #
    # Every position in the sequence must contain a vertex.
    #
    # For every position pos:
    #
    # p_v1_pos OR p_v2_pos OR ... OR p_vn_pos

    for pos in range(1, n+1):
        solver.append(
            Or([prop_vars[v][pos - 1] for v in vertices])
        )

    # Constraint 4:
    #
    # Two vertices that are NOT adjacent in the graph cannot
    # occur in consecutive positions in the sequence.
    #
    # For every pair of non-adjacent vertices vi and vk,
    # and every pair of consecutive positions j and j+1:
    #
    # NOT(p_i_j AND p_k_(j+1)), equivalent to p_i_j -> NOT(p_k_(j+1))

    for v1 in vertices:
        for v2 in vertices:
            if v1 != v2: # Only if i != j we check
                # If v1 and v2 are NOT connected by an edge,
                # they cannot be consecutive in the path.
                if v2 not in graph.get_adjacents(v1):
                    for pos in range(1, n):
                        solver.append(
                        Implies(
                            prop_vars[v1][pos - 1],
                            Not(prop_vars[v2][pos])
                        ))

    # Generate SMT-LIB2 script
    smt2 = solver.sexpr()
    smt2 += "\n(check-sat)\n(get-model)\n"

    with open("hamiltonian-path.smt2", "w") as f:
        f.write(smt2)

    # Check satisfiability
    if solver.check() == sat:
        # If it is satisfiable, we get the model
        model = solver.model()
        path = []
        # Find which vertex occurs at each position.
        for pos in range(1, n+1):
            for v in vertices:
                if is_true(model[prop_vars[v][pos - 1]]):
                    path.append(v)
                    break

        return path

    else:
        return None

# Example path given in the assigmnent:
# 1 -- 3 _
# |    |   5
# 2 -- 4 -
g = Graph(
    range(1, 6),
    [
        (1, 2),
        (1, 3),
        (2, 4),
        (3, 4),
        (3, 5),
        (4, 5)
    ]
)
path = has_hamiltonian_path(g)

if path is not None:
  print("Hamiltonian path:", path)
else:
  print("No Hamiltonian path exists.")