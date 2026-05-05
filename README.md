# fixed-rtrt

## Introduction

I encountered the problem in TAoCP Volume 4 §7.2.1.6, Ex. 17. and the solution
had an open question about classifying all of the families. I naively thought
it might be a short computational experiment.

## Lean project

This Lean project formalizes the classification attempt of a fixed set where
`RTRT f = f` or `RT f = TR f` holds for an ordered forest `f`. Instead of
dealing with unary nesting ((((())))) or leaf runs ()()()()()(), Donaghey's
"squeeze" is applied and fixed orbits no longer need to be parameterized by
integers.

The operators used below are Knuth's conjugation `R` and transpose `T`. The
conjugate `R` reverses forest order and recursively reverses child order inside
each tree. The transpose `T` is the tree/forest transpose determined by
`empty^T = empty` and `(S(A) B)^T = S(B^T) A^T`, where `S(A)` is the tree with
child forest `A` and `B` is the remaining forest. Both `R` and `T` are
involutions, and this repository writes `M = T R`.

## M2

This module sets up a nonelegant forest representation, implements Donaghey's
squeeze through `prim`, proves `prim (R f) = R (prim f)` (same for T) and
classifies the orbits by structural proofs. The remaining
conditional obstruction is the iterated equation below, which computationally
never gives forest `f` where `R f = f`.

This approach is simpler than not using `prim` as without `prim` it is
necessary to consume unary nesting and leaf runs and keep these integer
parameters available. With the parameters, we get a composition indexed
iterated equation which is hard to manage. With `prim` equation stays in `prim`
and is easy to compute.

There is also a proof that `RTRT f = f` implies `R f = f` and `TRT f = f`. This
speeds up compute, given that it's easy to generate R f = f forests instead of
full Catalan enumeration. In addition to that, we can directly enumerate
Donaghey's reduced trees, there's very little of them.

For example, fixed orbits appear at 1, 2, 5, 14 nodes. Checking that no fixed
orbits appear at n=42 is feasible and confirmed.

The iterated equation is much easier computational check than enumerating
forests and it somehow has no monotone quality or recurrence that would allow
us to prove a no-return theorem (equation says that particular forests arising
from iterated application are not R-fixed).

In the primitive-list model this obstruction is the sequence

```text
A_0 = []
A_{n+1} = R(T(A_n)) ++ [leaf].
```

The needed no-return statement is that `R(A_n) = A_n` only for the known small
indices; equivalently, no new primitive fixed family is hiding in this
iteration for `n >= 5`.

## M3

This module formalizes the result in Shapiro's "The Cycle of Six" paper in
addition to identifying remaining composition indexed families and their
formulas. Iterated equation that prevents full classification of the fixed set
is not included. The formalization was made before [this mathoverflow
question](https://mathoverflow.net/questions/510199/two-involutions-on-ordered-tree-forests-and-full-classification-of-fixed-set)
so it is not identical.

Infinite families are composition indexed, but as node count increases, the
composition gets more constrained, with the final families having composition
(2,...,2) as its core.

Using Knuth's "bar" operator (look below), the formulas for all ABCFGJK
families are available (or if not included, easy to discover).

The module uses a different forest representation that made it possible to have
short proofs that align with recursive definition of compositions.

## M^k

It is easy to use the operators and scripts to find formulas for infinite
families for arbitrary k. M^5 is very similar to M^2. Although very quickly no
orbits occur at all at higher k (primes). No proof was discovered as to why
they don't occur. For odd k there are no orbits with even node count (proof in
repo as well).

`primitive_mk_cuda` enumerates all primitive forests of a node size and checks
the general equation `M^k f = f` without the `R`-fixed shortcut used by the
specialized `primitive_rtrt_*` tools.

Examples:

```sh
make primitive_mk_cuda
./primitive_mk_cuda --k 2 --from 1 --to 17
```

The output reports primitive candidates, points fixed by `M^k`, orbit counts,
and the exact-period-`k` subset.

## Formalization methods

In addition to describing the proof sketch to Codex/ChatGPT Pro, Aristotle from
Harmonic was also used successfully to simplify or discover proofs, although
the tool could not handle structural arguments as easily as Codex (unary
nesting and leaf runs are easy to capture into an integer parameter in 1 step,
yet the Aristotle tool might unwrap the structure leaf by leaf or descent by
descent, creating an illusion of infinite descent).

## Knuth's exercises

The relevant TAoCP Volume 4, section 7.2.1.6 exercises are:

16. If `F` and `G` are forests, let `FG` be the forest obtained by placing the
    trees of `F` to the left of the trees of `G`; also let
    `F | G = (G^T F^T)^T`. Give an intuitive explanation of the operator `|`,
    and prove that it is associative. Answer:

    The point of `|` is to give ordinary concatenation a second coordinate
    system. Transpose changes which decomposition of a forest is easy to see:
    direct concatenation `FG` is the visible left-to-right product before
    applying `T`, while `F | G` is the product that is visible after applying
    `T`.  The reversed order in `(G^T F^T)^T` is exactly what makes transpose
    turn `|` back into plain concatenation:

    ```text
    (F | G)^T = G^T F^T.
    ```

    This is why the operator is useful in formulas for fixed families. It lets
    us assemble pieces in the transposed picture, then return to the original
    forest notation without carrying a large outer `T` through every formula.
    Concretely, expressions of the form `T(G^T F^T)` become `F | G`, and rules
    such as `F | L_n = S(F) L_{n-1}` turn a transpose-and-concatenate operation
    into a local forest construction. This is what keeps the ABCFGJK family
    formulas readable.

    Algebraically, `|` is just the product transported across the involution
    `T`, so associativity follows from involutivity of `T` and associativity of
    forest concatenation:

    ```text
    (F | G) | H = (H^T (F | G)^T)^T
                = (H^T G^T F^T)^T
                = F | (G | H).
    ```

17. Characterize all unlabeled forests `F` such that `F^{RT} = F^{TR}`. See
    exercise 14.

18. Two forests are said to be cognate if one can be obtained from the other by
    repeated operations of taking the conjugate and/or the transpose. The
    examples in exercises 11 and 12 show that all forests on 4 nodes belong to
    one of three cognate classes. Study the set of all forests with 15 nodes.
    How many equivalence classes of cognate forests do they form? What is the
    largest class? What is the smallest class? What is the size of the class
    containing `(2)`?

## Investigations

I've tried finding monotone quantities or different representations but none of
them can deal with the iterated equation and are equivalent to the equation on
ordered forests. Some quantities are 0 for n=0,1,2,4 and non-zero for others,
but no proof found that they never become 0 for higher `n`.

I also have raw formalization attempts in non-primitive forms that keep integer
parameterization of infinite families and discover their structure but it's
4k+ lines of Lean that I did not want to include in the project. Using `prim`
allows for simpler proofs and removes integer infinities and in the case of M3
it would also remove compositions.

Although, both approaches encounter the iterated equations so at least this
increases confidence that the equation is not an artifact of the proof method.

## References

[1] R. Donaghey, “Automorphisms on Catalan trees and bracketings,” J. Combin. Theory Ser. B 29 (1980), no. 1, 75–90. https://doi.org/10.1016/0095-8956(80)90045-3

[2] L. W. Shapiro, “The cycle of six,” Fibonacci Quart. 17 (1979), no. 3, 253–259. https://www.fq.math.ca/Scanned/17-3/shapiro.pdf

[3] D. E. Knuth, The Art of Computer Programming, Volume 4, Fascicle 4: Generating All Trees--History of Combinatorial Generation, Addison-Wesley, 2006, §7.2.1.6, Ex. 17.
