# -*- coding: utf8 -*-

# This file generates an SMT-LIB2 script for the coloring path problem

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

def can_color_graph(graph, k):
  colors = range(0, k)
  
  # For each pair (vertex, colour) we generate a Z3 boolean const
  # whose name is p_vertex_colour
  prop_vars = { x: [ Bool("p_%d_%d" % (x, c)) for c in colors] for x in graph.get_vertices() }
  
  solver = Solver()
  
  # Each vertex must have a colour.
  # For each i: p_i_1 \/ p_i_2 \/ .... \/ p_i_k
  
  for v in graph.get_vertices():
    solver.append(Or([prop_vars[v][c] for c in colors]))
  
  
  # Each vertex must have a single colour.
  for v in graph.get_vertices():
    for c in colors:
      solver.append(Implies(
        prop_vars[v][c],
        And([Not(prop_vars[v][c2]) for c2 in colors if c2 != c])
      ))
  
  # For each vertex 'i' and each color 'c', if i has c as its colour,
  # then the surrounding vertices must not have 'c' as its colour.

  # For each i and c: p_i_c => ¬p_j1_1 /\ ¬p_j2_c /\ ... /\ p_jn_c
  #
  # where {j1, ..., jn} are adjacent to i
  
  for v1 in graph.get_vertices():
    for c in colors:
      solver.append(
        Implies(prop_vars[v1][c], 
          And([Not(prop_vars[v2][c]) for v2 in graph.get_adjacents(v1)]))
        )
  
  
  # Generate SMT-LIB2 script separately
  smt2 = solver.sexpr()
  smt2 += "\n(check-sat)\n(get-model)\n"

  with open("colouring_graph.smt2", "w") as f:
    f.write(smt2)


  # Check satisfiability
  if solver.check() == sat:
    # If it is satisfiable, we get the model
    model = solver.model()
    color_map = {}
    # We traverse all the propositional variables, and check which ones
    # are true
    for v in graph.get_vertices():
      for c in colors:
        if is_true(model[prop_vars[v][c]]):
          color_map[v] = c
          break
    return color_map
  else:
    # If it is not satisfiable, return None
    return None
  
# Graph from the example given in the worksheet
g = Graph(range(1, 7), [(1, 4), (1, 2), (2, 5), (4, 5), (2, 3), (5, 6), (3, 6), (5, 3)])
print(can_color_graph(g, 3))