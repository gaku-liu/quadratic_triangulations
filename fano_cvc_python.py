import ast
import itertools
import cvc5
from cvc5 import Kind
import circuit

def mk_or(s, terms):
    if len(terms) == 0:
        return s.mkBoolean(False)
    elif len(terms) == 1:
        return terms[0]
    else:
        return s.mkTerm(Kind.OR, *terms)

def quadratic_triangulation(vertices, indices, all_circuits, all_nonunimodular):
    d = len(vertices[0])
    pairs = list(itertools.combinations(indices,2))
    circuits = []
    for c in all_circuits:
        if all(i in indices for i in c[0]) and all(i in indices for i in c[1]): 
            circuits.append(c)
    nonunimodular = []
    for simplex in all_nonunimodular:
        if all(i in indices for i in simplex):
            nonunimodular.append(simplex)
    edge_classes = {}
    for (i,j) in pairs:
        sum = tuple([vertices[i][k] + vertices[j][k] for k in range(d)])
        if sum in edge_classes.keys():
            edge_classes[sum].append((i,j))
        else:
            edge_classes[sum] = [(i,j)]
    
    s = cvc5.Solver()
    s.setOption("produce-models", "true")
    s.setOption("produce-proofs", "true")
    s.setLogic("QF_LRA")

    realSort = s.getRealSort()
    boolSort = s.getBooleanSort()

    h = {}
    for i in indices:
        h[i] = s.mkConst(realSort, f"h_{i}")

    x = {}
    for e in pairs:
        x[e] = s.mkConst(boolSort, f"x_{e}")

    for edges in edge_classes.values():
        # Exactly one edge in the class
        atleastone = mk_or(s, [x[e] for e in edges])
        s.assertFormula(atleastone)
        for e1, e2 in itertools.combinations(edges, 2):
            atmostone = s.mkTerm(Kind.NOT, s.mkTerm(Kind.AND,x[e1],x[e2]))
            s.assertFormula(atmostone)

        # Chosen edge is minimum in edge class
        for (i,j) in edges:
            for (k,l) in edges:
                if (i,j) != (k,l):
                    ineq = s.mkTerm(Kind.LT, s.mkTerm(Kind.ADD,h[i],h[j]), s.mkTerm(Kind.ADD,h[k],h[l]))
                    min = s.mkTerm(Kind.IMPLIES, x[i,j], ineq)
                    s.assertFormula(min)

    # At least one missing edge in a part of each circuit.
    for c in circuits:
        edges1 = itertools.combinations(c[0],2)
        edges2 = itertools.combinations(c[1],2)
        edges = list(itertools.chain(edges1, edges2))
        somemissing = mk_or(s, [s.mkTerm(Kind.NOT,x[e]) for e in edges])
        s.assertFormula(somemissing)
    
    # At least one missing edge in each nonunimodular simplex
    for simplex in nonunimodular:
        edges = list(itertools.combinations(simplex,2))
        somemissing = mk_or(s, [s.mkTerm(Kind.NOT,x[e]) for e in edges])
        s.assertFormula(somemissing)

    status = s.checkSat()
    if status.isSat():
        print("Quadratic triangulation found")
        heights = {i:s.getValue(h[i]) for i in indices}
        with open('heights_test.txt', 'w') as f:
            for i in indices:
                f.write(f"{vertices[i]}: " + str(heights[i]) + "\n")
    elif status.isUnsat:
        print("Proven no quadratic triangulation")
        proof = s.getProof()
        with open('proof_test.txt', 'w') as f:
            for line in proof:
                f.write(str(line))
    else:
        print("Could not resolve")
    
    return status

def main():
    vertices = [(0,0,0),(1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,0,1),(0,1,1),(1,1,1)]
    indices = (0,4,5,6,7)
    circuits = circuit.get_affine_circuits(vertices)
    nonunimodular = [(0,4,5,6),(1,2,3,7)]
    quadratic_triangulation(vertices, indices, circuits, nonunimodular)

def main1():
    # In order, matroid elements are
    # 001, 010, 011, 100, 101, 110, 111
    fano = [(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0),(1,1,1)]

    # Creates the list of vertices. Vertices are stored as tuples.
    vertices = []
    for i in range(5):
        for j in range(i+1,6):
            for k in range(j+1,7):
                if not all((fano[i][t] + fano[j][t] + fano[k][t]) % 2 == 0 for t in range(3)):
                    vertex = [0] * 7
                    vertex[i] = 1
                    vertex[j] = 1
                    vertex[k] = 1
                    vertices.append(tuple(vertex))
    n = len(vertices)

    # minor is some subset of the vertices
    minor = [i for i in range(n) if vertices[i][0] == 0]
    # minor = range(n)

    # Reads all circuits and puts them in a list. Circuits are stored as (c[0], c[1]), where c[i] is
    # a tuple with all vertices in that part.
    circuits = []
    with open('circuitsFano.txt', 'r') as file:
        for line in file.readlines():
            circuit = ast.literal_eval(line)
            circuit = (tuple(sorted(circuit[0])), tuple(sorted(circuit[1])))
            circuits.append(circuit)

    # Stores all minimal nonunimodular simplices as tuples.
    nonunimodular = []
    with open('minimal_nonunimodular_simplices.txt', 'r') as file:
        for line in file.readlines():
            simplex = ast.literal_eval(line)
            nonunimodular.append(simplex)

    quadratic_triangulation(vertices, minor, circuits, nonunimodular)

if __name__ == "__main__":
    main()


    




