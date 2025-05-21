## Handshaking Lemma

### Statement

\\(\sum d(x) = 2e(G)\\)

### Proof

For each edge, place a stone at the end vertices, then each vertex has exactly \\(d(v)\\) stones and we have placed exactly \\(2e(G)\\) stones.

## Average degree subgraph:

### Statement

Every graph has a subgraph H such that \\(\delta(G) \geq d(H)/2 \geq d(G)/2\\)

### Proof

- If \\(d_F(v) < d(F)/2\\), then \\(d(F - v) > d(F)\\)
- Thus repeatedly remove all vertices
- Either this reaches a state satisfying the conditions or we reach the graph with one vertex, clearly this has average degree of 0, less than previous contradiction

## Minimum degree is path/cycle

### Statement

G contains a path of length of at least \\(\delta(G)\\) and if \\(\delta(G) \geq 2\\) then G contains a cycle of length at least \\(\delta(G) + 1\\)

### Proof

Assume longest path
End vertices have all edges inside the path
Thus cycle can be formed by \\(\delta(x_1) + 1\\) vertex and the path

## Connected \\(\iff\\) spanning tree

### Statement

A graph \\(G\\) is connected if and only if it contains a spanning tree

### Proof

\\(\implies\\) Remove all vertices in cycles become tree on same vertices
\\(\impliedby\\) \\(T\\) connected, add edges to form \\(G\\) maintaining connectivity

## Tree has 2 leaves

### Proof

Assume path of longest length, then end vertices are leaves:
if they connect into the path a cycle is formed and no longer tree

## Tree has \\(|T| - 1\\) edges

### Proof

Induction on \\(T\\)

In induction step remove leaf, then \\(\|T\| - 2\\) edges, we add leaf on and it has \\(\|T\| - 1\\) edges.

## Graph bipartite \\(\iff\\) \\(G\\) has no cycle of odd length

### Proof

\\(\implies\\) Obvious by cycle construction
\\(\impliedby\\) constuct based on MST
- choose some vertex
- make bipartite sets based on odd or even path length from this
- if \\(xx'\\) edge with \\(x, x'\\) in same set, then we can make an odd cycle contradiction

## Every graph has bipartite subgraph with at least \\(e(G)/2\\) edges

### Proof

Take partition \\(H = G[X, Y]\\) with \\(e(H)\\) maximal
Claim that vertex \\(v\\) satisfies \\(d_H(v) \ge d_G(v)/2\\)
Otherwise we can claim a contradiction based on edges without \\(v\\):
\\(e(H - v) \ge e(H) - d_H(v) + (d_G(v) - d_H(v)) > e(H)\\)

## Hall's Theorem *

### Statement

A bipartite graph \\(G = (A, B, E)\\) has a matching covering \\(A\\) if and only if Hall's condition holds.

### Proof

\\(\implies\\) Use matching to show that \\(|\Gamma(S)| >= |S|\\) for some subset S of A
\\(\impliedby\\) Induction on \\(A\\)
    We then see that for all proper subsets we have \\(|\Gamma(S)| > |S|\\)
        - Here we look at \\(G' = G - \{x, y\}\\) for some vertices \\(x, y\\) then clearly this satisfies Hall's condition
    or there are some subsets such that \\(|\Gamma(S)| = |S|\\)
        - I'll be honest if we have to parrot this I am fucked

## \\(k\\)-regular bipartite graph contains perfect matching

### Proof

Satisfies Hall's condition:

\\(\|S\|k = \sum_{v \in S} d(v) = e_G(S, N(S)) \le \sum_{v \in \Gamma(S)} d(v) \le \|\Gamma(S)\|k\\)

Thus
\\(|S| \le |\Gamma(S)|\\)

## Deficient Hall

### Proof

Add \\(d\\) new vertices to the vertex class \\(B\\), with new vertices adjacent to everything in \\(A\\).

Then we can show that Hall's condition holds and we have at least the required matching.

## König's Theorem *

### Proof

\\(\|X\| \ge \|M\|\\) simple

\\(\|M\| \ge \|X\|\\):

- If this comes up I'm gonna die anyway

## Tutte's Theorem (forwards implication)

### Proof

\\(\implies\\) Removes at most \\(\|S\|\\) edges, so \\(q(G - S) \le \|S\|\\)

## Matching limit on edge size

### Statement

Suppose that \\(G\\) is an \\(n\\)-vertex graph which does not contain a matching of size \\(k + 1\\), then \\(e(G) \le 2kn\\).

### Proof

Induction on \\(k\\)

At induction step assume \\(e(G) > 2kn\\), then \\(e(G - \{x, y\}) \ge 2kn - (n - 1) - (n - 2)\\) and thus contains a matching of size \\(k\\), adding one edge \\(xy\\) we have a matching of size \\(k + 1\\).

## Erdős-Gallai *

I'm fucked if this comes up (maybe)

## Gale-Shapely Works

### Proof

**Gives Matching**

Assume doesn't, then two people aren't in matching
- but \\(x\\) has proposed to everyone
- thus \\(y\\) has been proposed to so should be on edge with someone

contradiction.

**Is Stable**

Assume by contradiction two edges wish to swap, then \\(a\\) ranks \\(b'\\) higher than \\(b\\) and \\(b'\\) ranks a higher than \\(a'\\), but a girls ranking of her suitor can only ever increase so we reach a contradiction.

## Whitney *

### Proof

- \\(\lambda(G) \le \delta(G)\\): take \\(v\\) where \\(d(v) = \delta(v)\\), then clearly \\(G\\) - those vertices is disconnected thus \\(\lambda(G) \le \delta(G)\)

- \\(\kappa(G) \le \lambda(G)\\): kinda fucked

## Menger's Theorem - Local *

### Proof

maximum internally disjoint paths \\(\le\\) minimise size of separator

Must at least one vertex from each path.

other way is fucked up

## Menger's Theorem Global Version

### Proof

If \\(ab\\) is an edge, we then remove it - then can see that the graph is \\(k - 1\\) connected, giving us \\(k - 1\\) paths and thus \\(k\\) paths with the edge \\(ab\\).

## Menger's Edge Version

### Proof

Form \\(L(G)\\) and add \\(a', b'\\) which are adjacent to edges where \\(a\\) in edge \\(e\\) and \\(b\\) in edge \\(e\\)
- If \\(W\\) is a separator for \\(G\\), then is is an \\(a'-b'\\) separator in \\(L(G)\\) modified
- Internal vertices of \\(a'b'\\) path contains edges of \\(ab\\)-path in \\(G\\)

By Menger's Local, we have separator same size as paths.

## Mader's Theorem *

### Proof

Long and minging

## Lemma 3.23

### Statement

Any graph \\(G\\) with average degree \\(d(G) \ge h2^m\\) contains a subdivision of every graph \\(H\\) with \\(\|H\| = h\\) and \\(e(H) = m\\).

### Proof

Induction on \\(m\\)

Induction step
\\(H' = H - uv\\) for \\(uv\\) in \\(E(H)\\).

Take \\(U \subseteq V(G)\\) maximal such that

- \\(G[U]\\) connected
- \\(G \setminus U\\) has \\(d(G/U) \ge h2^m\\)

We claim that \\(G' = G[\Gamma(U)\setminus U]\\) satisfies \\(\delta(G') \geq h2^{m-1}\\)

If not true, then we have some \\(w\\) such that \\(d(w) < h2^{m-1}\\) which contradicts maximality.

As \\(G'\\) has \\(d(G') \geq h2^{m-1}\\) by induction, there is a subdivision of \\(H'\\), \\(\tilde{H}\\), then take \\(u', v'\\) (branch vertices corresponding to \\(u, v\\)). Take this path with \\(\tilde{H}\\), then we have the subdivision of \\(H\\).

## Lower bound on chromatic number

\\(\chi(G) \ge \max \{\omega(G), \|G\|/\alpha(G)\}\\)

### Proof

We need \\(r = \omega(H)\\) colours to colour the clique.
Now look at colour classes of \\(G\\), maximum size of each is \\(\alpha(G)\\) so

\\(\|G\| \le \chi(G) \alpha(G)\\)

## Upper bound on chromatic number

\\(\chi(G) \le \max \{\delta(H) : H \subseteq G\} + 1 \le \Delta(G) + 1\\)

### Proof

Take enumeration where we choose the vertex of lowest degree at each point, then greedy algorithm chooses at most \\(\delta(H) + 1\\).

## Connected graph has enumeration such that every vertex has a neighbour behind it

### Proof

Since \\(G\\) connected, there is a vertex connected to \\(x_n\\), then vertex joined to one of \\(x_n, x_{n - 1}\\), and so on.

## 3-connected graph has \\(\chi(G) \le \Delta(G)\\)

### Proof

**Claim** There are vertices \\(x, y, z \in V(G)\\) such that \\(xy, xz \in E(G)\\) bu \\(yz \notin E(G)\\).

Take minimal path between two non-adjacent vertices, then choose \\(x = v_2, y = v_1, z = v_3\\), notice that \\(v_1v_3\\) not an edge because otherwise we have a shorter path.

Now we can use the enumeration with at least one neighbour behind on all vertices apart from \\(x\\) and \\(y\\).
We then give the ordering with \\(x, y\\) at the start, which uses 1 colour because these are not adjacent.
Each subsequent vertex has at most \\(\Delta(G) - 1\\) neighbours coloured so uses at most \\(\Delta(G)\\) colours.
The last vertex has at most \\(\Delta(G)\\) neigbours, but two of these are \\(x, y\\) so we can colour it with at most \\(\Delta(G)\\).

## König - bipartite *

### Proof

Induction on \\(e(G)\\).

Induction step

Remove any edge.

## Euler

### Proof

Induction of f.

Induction step - remove edge, then E = E - 1, F = F - 1 and works

## Upper bound on planar graph edges

### Proof

length(F) >= 3 so 2e(G) >= 3f.

Then apply eulers rearranging for e(G).

If K_3 not in there - length(F) >= 4.

## \\(K_3\\) and \\(K_{5, 5}\\) not planar

### Proof

Apply the upper bound limit.

## Planar graph has vertex of degree at most five

### Proof

Suppose that \\(delta(G) \ge 6\\), then

\\(2e(G) \ge 6\|G\|\\)

so \\(e(G) \ge 3\|G\|\\) - contradiction.

## \\(\chi(G) \le 6\\)

### Proof

1.

Take min degree in \\(G\\), we know that \\(d(v) \le 5\\). Thus when readding we don't increase the colouring.

2. 
\\(\delta(H) \le 5\\) for all subgraphs \\(H\\) of \\(G\\). Thus \\(\chi(G) \le \max \{ \delta(H) : H \subseteq G\} + 1 \le 6\\).

## \\(\chi(G) \le 5\\) *

### Proof

...

## G - S has at most |S| components, where G is Hamiltonian.

### Proof

Cycle has to visit every component of G - S at least once, no edges between components, therefore when leaving a component we have to go to S, with these vertices distinct, thus number of arrival vertices >= components. I.e. components <= \|S\|.

## Hamilton iff s = t >= 2

### Proof

G - S can have more than \|S\| components (choose smallest set) for s != t so G is not Hamiltonian

## Dirac

### Proof

**Graph is Connected**

Take \\(x, y\\) where \\(xy \notin E(G)\\), then consider \\(\|N(x) \cap N(y)\|\\) (it's 2).

**Graph has a cycle**

Take the longest path, then this is a cycle.

Take successors of neighbours of \\(x_0\\) and successors of neighbours of \\(x_k\\). Notice that there at most \\(n-2\\) vertices internally and \\(n/2\\) in both the successors of \\(N(x_k)\\) and \\(n/2\\) in \\(N(x_0)\\).

Call this vertex \\(x_i\\).

We can therefore form a cycle \\(x_0x_iPx_kx_{i-1}Px_0\\).

**Cycle is Hamiltonian**

Suppose \\(V(C) < V(G)\\) then path \\(P' = (C - vw) \cup vw\\) is loger than \\(P\\). A contradiction.
 

## Ore

### Proof

Modified Dirac.

## Ore Variant *

### Proof

Modified Dirac.

## Chvátal-Erdős *

...

## No path of length \\(k, e(G) \le \frac{(k-1)n}{2}\\)

Induct on \\(n\\). Holds if \\(n \le k\\).

If \\(G\\) disconnected, then induction holds for all smaller components. We can therefore assume \\(G\\) is connected.

Take \\(x\\) with \\(d(x) \le (k-1)/2\\), so \\(e(G - x) < (k-1)(n-1)/2\\) hence

\\(e(G) = e(G - x) + d(x) < ... = (k-1)/2\\)

## Mantel

### Proof

Induction on \\(n\\).

Induction step

Suppose \\(K_3\\)-free. For any pair of edges, \\(N(x) \cap N(y) = \emptyset\\). Thus \\(d(x) + d(y) \le n\\). Remove an edge \\(xy\\), then

\\[
e(H) = e(G) - (d(x) + d(y) - 1) > \frac{n^2}{4} - n + 1 = \frac{(n-2)^2}{4}
\\]

Thus \\(H\\) (and therefore \\(G\\)) contains a copy of \\(K_3\\).

## \\(r\\)-partite graph then \\(G = T_r(n)\\) or \\(e(G) < e(T_r(n))\\) <--

...

## For all k, g >= 3, there is G with chi(G) >= k and no cycles of length fewer than g

...

## e(T_r(n)) = e(T_r(n - r)) + binom(r)(2) + (n - r)(r - 1)

...

## Túran's theorem (Nope)

...

## Turan density decreases

...

## Turan density lower bound

...

## Upper bound on bipartite Túran Number

... (starry guys)

## P(e(G) >= 1/2 p binom(n)(n)) >= 1/2

...

## Lower bounds on ex(n, K_{s, t})

...

## k-partite subgraph with e(H) >= (k-1)e(G)/k

...

## Sum for a(G)

...

## Upper bound on ex(n, K_{r + 1}) <= {(r-1)n^2}/{2r}

...

## cr(G) >= m = k, n >= 3 then cr(G) >= m - 3n + 6

...

## m >= 4n, then cr(G) >= m^3/(64n^2)

...
