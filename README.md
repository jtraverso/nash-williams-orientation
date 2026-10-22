# Nash-Williams' weak orientation theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of the weak orientation theorem of C. St. J. A. Nash-Williams
(*On orientations, connectivity and odd-vertex-pairings in finite graphs*, Canad. J. Math. 12
(1960) 555–567): every `2k`-edge-connected finite graph has an orientation that is
`k`-arc-connected, that is, every nonempty proper set of vertices is left by at least `k` arcs.
For `k = 1` this is Robbins' theorem. All statements are in the namespace
`NashWilliamsOrientation` of `Challenge.lean`.

## Definitions

* A finite loopless multigraph on `V` is an edge family `ends : ι → V × V` over a finite index
  type `ι` (parallel edges allowed); an orientation is `o : ι → Bool`, orienting edge `i` from
  `(ends i).1` to `(ends i).2` when `o i` holds and the other way otherwise.
* `cut ends S`: the number of edges with exactly one endpoint in `S`.
* `outCut ends o S`: the number of arcs leaving `S` under the orientation `o`.
* For simple graphs, the statement uses Mathlib's `SimpleGraph.IsEdgeConnected` and represents
  an orientation as a Mathlib `Digraph` whose underlying graph
  (`Digraph.toSimpleGraphInclusive`) is `G` and which never contains both `u → v` and `v → u`.

## Results

| Lean | Statement |
|---|---|
| `nash_williams` | If every nonempty proper `S ⊆ V` has `cut ends S ≥ 2k`, there is an orientation `o` with `outCut ends o S ≥ k` for every nonempty proper `S` |
| `nash_williams_simple` | Every finite `2k`-edge-connected simple graph (on a nonempty vertex type) has an orientation in which every nonempty proper `S` has at least `k` arcs from `S` to its complement |

## Proof

The proof (`NashWilliamsLib/`) is by strong induction on the number of edges.

* If some edge can be deleted without destroying `2k`-edge-connectivity, it is deleted, the
  rest is oriented by induction, and that edge is oriented arbitrarily.
* Otherwise the multigraph is minimally `2k`-edge-connected. By Mader's lemma (`Mader.lean`,
  proved by uncrossing with the submodularity of the cut function in `Basic.lean`) it has a
  vertex `s` of degree exactly `2k`.
* Lovász's splitting lemma (`Splitting.lean`) splits the `2k` edges at `s` into `k` pairs
  `(su, sv) ↦ uv`, keeping every cut of the remaining vertices of size at least `2k`.
* The smaller multigraph is oriented by induction (`Orientation.lean`). Each new arc `u → v` is
  replaced by `u → s → v`, so no cut loses an outgoing arc.

The simple-graph version follows by viewing each edge of `G` as a multigraph edge. No `sorry`
and no `native_decide` is used; the only axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the audited statements. It imports
  only Mathlib.
- [`Solution.lean`](Solution.lean) and [`NashWilliamsLib/`](NashWilliamsLib): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## Sources

* C. St. J. A. Nash-Williams, *On orientations, connectivity and odd-vertex-pairings in finite
  graphs*, Canad. J. Math. 12 (1960) 555–567, doi:10.4153/CJM-1960-049-6.
* L. Lovász, *On some connectivity properties of Eulerian graphs*, Acta Math. Acad. Sci. Hungar.
  28 (1976) 129–138, doi:10.1007/BF01902503.
* W. Mader, *A reduction method for edge-connectivity in graphs*, Ann. Discrete Math. 3 (1978)
  145–164, doi:10.1016/S0167-5060(08)70504-1.

## Authorship and use of AI

The author chose the result and directed the work. The proofs were produced by Harmonic's
Aristotle from formal statements and a suggested proof route. Claude (Claude Code) wrote the
statements, audited the return, built it locally and prepared this package. Lean checks
everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
