#import "@preview/cetz:0.1.2": canvas, draw, tree
#import "@preview/commute:0.2.0": node, arr, commutative-diagram

#import "../template/template.typ": notes

#show: notes.with(
  title: "Formal Methods Notes",
  authors: (
    "Clemens Koza, 01126573",
  ),
)

#[
  #set heading(numbering: none)

  = Revision history

  - no "published" version yet.

  = About this document

  This document is based on the Formal Methods in Informatics lecture at Vienna University of Technology; particularly from taking it in the 2023/24 winter term. Corrections and additions are welcome as pull requests at

  https://github.com/SillyFreak/tu-wien-software-engineering-notes

  This document leaves out several details and was written primarily for me, but I hope it is useful for other people as well.

  If you have questions, feel free to reach out on Github. I may at least occasionally be motivated enough to answer questions, extend the document with explanations based on your question, or help you with adding it yourself.

  #pagebreak()
]

= Tseitin translation

The Tseitin translation's purpose is to transform an arbitrary propositional formula into a conjunction of disjunctions (clauses), which can then be fed to a typical SAT solver. In contrast to the CNF, the resulting formula is linear in the input formula's length.

Following, we will translate the example formula from the lecture slides:

$ phi: (p and q -> r) -> (q -> r) $

== Labelling of subformula occurrences (SFOs)

In the tree representation of the formula, every subformula receives a new atom. That new atom is set equivalent to the subformula; if the subformula is not itself atomic, the branches of the subformula are themselves replaced by new atoms.

#grid(
  columns: (1fr,)*2,
  rows: auto,
  gutter: 3pt,
  {
    set align(center)

    let data = (
      $->$,
      ($->$, ($and$, $p$, $q$), $r$),
      ($->$, $q$, $r$),
    )

    let add-labels(data, accum: 0) = {
      if type(data) != array {
        accum += 1
        ((data: data, label: accum), accum)
      } else {
        let (root, ..branches) = data

        // iterate over branches
        for i in range(1, data.len()) {
          let branch = data.at(i)
          let (branch, new-accum) = add-labels(branch, accum: accum)
          accum = new-accum
          data.at(i) = branch
        }
        // transform root
        accum += 1
        data.at(0) = (data: data.at(0), label: accum)
        (data, accum)
      }
    }

    let data = add-labels(data).at(0)

    canvas({
      import draw: *

      set-style(stroke: 0.45pt)

      tree.tree(
        data,
        padding: 0.8,
        spread: 0.8,
        grow: 1.2,
        draw-node: (node, _) => {
          let (data, label) = node.content
          let label = text(blue, 0.8em)[$ell_#label$]
          let label = move(dx: -14pt, dy: -8pt)[#label]
          let label = box(width: 0pt)[#label]
          content((), [#data#label])
        },
        draw-edge: (from, to, _) => {
          line((a: from, number: .5, abs: true, b: to),
              (a: to, number: .5, abs: true, b: from))
        },
        name: "tree",
      )
    })
  },
  [
    #show math.attach: it => {
      if it.base.text == $ell$.body.text {
        text(blue, it)
      } else {
        it
      }
    }

    $
    ell_1 &<-> p \
    ell_2 &<-> q \
    ell_3 &<-> ell_1 and ell_2 \
    ell_4 &<-> r \
    ell_5 &<-> ell_3 -> ell_4 \
    ell_6 &<-> q \
    ell_7 &<-> r \
    ell_8 &<-> ell_6 -> ell_7 \
    ell_9 &<-> ell_7 -> ell_8 \
    $
  ],
)

We can easily see that subformula $p$ is satisfiable iff $(ell_1 <-> p) and ell_1$ is satisfiable: substituting the left clause into the right one, we are left with exactly $p$. This conjunction of the new atom and the corresponding equivalence clause thus captures the satisfiability of the original subformula. Likewise, for a more complex subformula like $p and q$, we can take $(ell_1 <-> p) and (ell_2 <-> q) and (ell_3 &<-> ell_1 and ell_2) and ell_3$ and get the same result. Applying this to the whole formula $phi$, we get

$
(ell_1 <-> p) and dots and (ell_9 &<-> ell_7 -> ell_8) and ell_9
$

This formula has three crucial properties:

- as stated above, it is satisfiable iff $phi$ is satisfiable (although not logically equivalent because it contains new atoms),
- its length is linear in terms of the length of $phi$, and
- it is essentially _flattened_, which means that the linearity in length will be preserved when transforming it to CNF.

== Generating clauses for the CNF

SAT solvers by convention accept formulas as a set of clauses over a set of atoms. To make the above result usable by such a tool, we need to convert it into this form. Since we have constructed a flat set of equivalence clauses, we can enumerate all possible forms of clauses and how they are translated into CNF. For example:

$
&ell_i <-> x         &&equiv (ell_i -> x)         &&and (ell_i <- x)         &&equiv (not ell_i or x) and (ell_i or not x) \
&ell_i <-> (x and y) &&equiv (ell_i -> (x and y)) &&and (ell_i <- (x and y)) &&equiv (not ell_i or x) and (not ell_i or y) and (ell_i or not x or not y) \
&ell_i <-> (x -> y)  &&equiv (ell_i -> (x -> y))  &&and (ell_i <- (x -> y))  &&equiv (not ell_i or not x or y) and (ell_i or x) and (ell_i or not y) \
$

The equivalence of these formulas can be easily verified using a truth table; I find splitting equivalences into two implications useful as an intermediate step to more easily see the CNF clauses. We can now finally translate our formula into a _definitional form_ that is in CNF:

$
(not ell_1 or p) and (ell_1 or not p) and dots and (not ell_9 or not ell_7 or ell_8) and (ell_9 or ell_7) and (ell_9 or not ell_8) and ell_9
$

Or, as a set of clauses instead of a formula:

$
delta(phi) = hat(delta)(phi) union {ell_9} = {not ell_1 or p, ell_1 or not p, dots, not ell_9 or not ell_7 or ell_8, ell_9 or ell_7, ell_9 or not ell_8, ell_9}
$

= Implication Graphs

Implication graphs capture aspects of the logical structure of a set of clauses that are useful for efficiently computing satisfiability of that set of clauses. We will first define some preliminaries, then implication graphs themselves, and then look at some examples.

== Clause states

A clause can have one of four states:

- _satisfied:_ at least one of its literals is assigned true
- _unsatisfied:_ all its literals is assigned false
- _unit:_ all but one literals is assigned false (i.e. the last needs to be assigned true to be satisfied, the decision is forced)
- _unresolved:_ none of the above

== Decisions

Decisions add variable assignments to a partial variable assignment. Depending on when in the process a variable is assigned, a decision has a _decision level_. By deciding one variable per level, decision levels (for regular decisions) range from 1 at most to the number of variables - usually, it will be less, because decisions on unit clauses are forced.

We write $x = v@d$ to say that variable $x$ has been assigned value $v$ at decision level $d$. As a shorthand for $x = 1@d$/$x = 0@d$, we write $x@d$/$not x@d$ (or $ell@d$: deciding a literal at depth $d$, where the literal is a negated or non-negated variable). The _dual_ $ell^d$ (or $ell^d@d$) means the opposite decision of $ell$ (or $ell@d$), e.g. the dual of $x@d$ is $not x@d$ and vice-versa.

== Antecedents

Under a partial variable assignment $sigma$, a clause $C$ may simplify to a unit clause $ell$, which we write $C sigma = ell$. For example, under the partial variable assignment $sigma = { x_1 |-> 1, x_4 |-> 0}$, the clause $C: not x_1 or x_4 or not x_3$ simplifies to $not x_3$.

The clause that, under some $sigma$, forces a decision of $ell$ is called its _antecedent_: $"Antecedent"(ell) = C$. Here, $C$ is treated as a set of literals (i.e. ${not x_1, x_4, not x_3}$). Although it should not matter for the construction of implication graphs, when a literal is not forced under some partial assignment, we can simply take the antecedent to be an empty set.

== The implication graph

An implication graph (IG) is a DAG $G = (V, E)$ that satisfies:

- Each vertex has a label of the form $ell@d$, where $ell$ is some literal and $d$ is a decision level.
- For each vertex $v_j$, take the set of dual literals of its antecedent: ${v_i | v_i^d in "Antecedent"(v_j)}$. For all $v_i$ that are vertices of the graph, there is an edge from $v_i$ to $v_j$, or: $E = {(v_i, v_j) | v_i, v_j in V, v_i^d in "Antecedent"(v_j)}$. All these edges are labelled with $"Antecedent"(v_j)$.
  - The way IGs are constructed, all but one $v_i$ _will_ label a vertex in the graph, or equally: the clause $"Antecedent"(v_j)$ is unit and the edges completely decribe why $v_j$ was forced; unforced literals don't have incoming edges. The only $v_i$ that thus didn't label a vertex is $v_j^d$. If that existed, this leads to the other option:

Conflict graphs are also implication graphs, and they contain additionally

- one vertex labelled $kappa$ called the conflict node, and
- edges ${(v, kappa) | v^d in c}$ for some clause $c$.
  - Note that there's no "filter" $v in V$ in this definition, so all of $c$'s literals' duals need to actually be vertices, which makes the clause actually unsatisfied and $kappa$'s predecessor nodes conflicting.

Implication graphs are created incrementally by deciding one variable, resolving any unit clauses resulting from that assignment (by boolean constraint propagation or BCP), and repeating that until either all variables are assigned or a conflict is found.

== Example 1

Let's take the single clause $c: not x_1 or x_4 or not x_3$ again and start from zero.

- Arbitrarily we begin by assigning $x_1 |-> 1$, or with the decision $x_1@1$.
- After this decision, we have no unit clause and continue with $x_4 |-> 0$ or $not x_4@2$. At this point, $c$ can be simplified to $not x_3$, meaning we have $"Antecedent"(not x_3) = {not x_1, x_4, not x_3}$.
- We thus add a vertex $not x_3@2$ (at the same depth as the decision that made the clause unit) and two edges $(x_1@1, not x_3@2)$, $(not x_4@2, not x_3@2)$ to the graph.
- All variables have been assigned without conflict; we're done.

#grid(
  columns: (auto,)*3,
  rows: auto,
  gutter: 1fr,
  [
    #set align(center)
    #commutative-diagram(
      node-padding: (32pt, 16pt),
      node((0, 0), [$x_1@1$]),
      // node((2, 0), [$not x_4@2$]),
      // node((1, 1), [$not x_3@2$]),
      // arr((0, 0), (1, 1), [$C$]),
      // arr((2, 0), (1, 1), [$C$]),
    )
  ],
  [
    #set align(center)
    #commutative-diagram(
      node-padding: (32pt, 16pt),
      node((0, 0), [$x_1@1$]),
      node((2, 0), [$not x_4@2$]),
      // node((1, 1), [$not x_3@2$]),
      // arr((0, 0), (1, 1), [$C$]),
      // arr((2, 0), (1, 1), [$C$]),
    )
  ],
  [
    #set align(center)
    #commutative-diagram(
      node-padding: (32pt, 16pt),
      node((0, 0), [$x_1@1$]),
      node((2, 0), [$not x_4@2$]),
      node((1, 1), [$not x_3@2$]),
      arr((0, 0), (1, 1), [$c$]),
      arr((2, 0), (1, 1), [$c$]),
    )
  ],
)

== Example 2

Let's assume that we had not made decisions one after the other (and thus resolved $c$ that became a unit clause) but came up instantly with the assignment ${x_1@1, not x_4@1, x_3@1}$. This would make $c$ unsatisfied and lead to a conflict graph:

#[
  #set align(center)
  #commutative-diagram(
    node-padding: (48pt, 24pt),
    node((0, 0), [$x_1@1$]),
    node((1, 0), [$not x_4@1$]),
    node((2, 0), [$x_3@1$]),
    node((1, 1), [$kappa$]),
    arr((0, 0), (1, 1), [$c$]),
    arr((1, 0), (1, 1), [$c$]),
    arr((2, 0), (1, 1), [$c$]),
  )
]

== Example 3

To arrive at a conflict organically, we need a set of clauses that can be refuted such as $c_1: x or y$, $c_2: x or z$, $c_3: not y or not z$. We start by assigning $x |-> 0$ and are forced from there:

#grid(
  columns: (auto,)*4,
  rows: auto,
  gutter: 1fr,
  [
    #set align(center)
    #commutative-diagram(
    node-padding: (40pt, 20pt),
      node((1, 0), [$not x@1$]),

      // node((0, 1), [$y@1$]),
      // arr((1, 0), (0, 1), [$c_1$]),

      // node((2, 1), [$z@1$]),
      // arr((1, 0), (2, 1), [$c_2$]),

      // node((1, 2), [$kappa$]),
      // arr((0, 1), (1, 2), [$c_3$]),
      // arr((2, 1), (1, 2), [$c_3$]),
    )
  ],
  [
    #set align(center)
    #commutative-diagram(
    node-padding: (40pt, 20pt),
      node((1, 0), [$not x@1$]),

      node((0, 1), [$y@1$]),
      arr((1, 0), (0, 1), [$c_1$]),

      // node((2, 1), [$z@1$]),
      // arr((1, 0), (2, 1), [$c_2$]),

      // node((1, 2), [$kappa$]),
      // arr((0, 1), (1, 2), [$c_3$]),
      // arr((2, 1), (1, 2), [$c_3$]),
    )
  ],
  [
    #set align(center)
    #commutative-diagram(
    node-padding: (40pt, 20pt),
      node((1, 0), [$not x@1$]),

      node((0, 1), [$y@1$]),
      arr((1, 0), (0, 1), [$c_1$]),

      node((2, 1), [$z@1$]),
      arr((1, 0), (2, 1), [$c_2$]),

      // node((1, 2), [$kappa$]),
      // arr((0, 1), (1, 2), [$c_3$]),
      // arr((2, 1), (1, 2), [$c_3$]),
    )
  ],
  [
    #set align(center)
    #commutative-diagram(
    node-padding: (40pt, 20pt),
      node((1, 0), [$not x@1$]),

      node((0, 1), [$y@1$]),
      arr((1, 0), (0, 1), [$c_1$]),

      node((2, 1), [$z@1$]),
      arr((1, 0), (2, 1), [$c_2$]),

      node((1, 2), [$kappa$]),
      arr((0, 1), (1, 2), [$c_3$]),
      arr((2, 1), (1, 2), [$c_3$]),
    )
  ],
)

_Sneak peek into CDCL:_ our decision of $not x@1$ led to a conflict here (in general, there could be multiple unforced decisions, but here it's just one), so we know that that is a decision we _must not_ make. We thus need to backtrack to before that decision (in this case: before _any_ decision) and prevent ourselves from making that mistake again.

The way this is done is by adding a clause that captures the wrong decision, i.e. $c_4: x$. Because here, we only had one unforced decision, this is already a unit clause, and we're forced to decide $x@0$ (i.e. before the first regular decision).

After that, no clause is unit ($c_1$, $c_2$, $c_4$ are satisfied, $c_3$ is unresolved) so we can make a decision such as $y@1$, which forces a decision on $z$:

#grid(
  columns: (auto,)*3,
  rows: auto,
  gutter: 1fr,
  [
    #set align(center)
    #commutative-diagram(
    node-padding: (40pt, 20pt),
      node((0, 0), [$x@0$]),

      // node((1, 0), [$y@1$]),

      // node((1, 1), [$not z@1$]),
      // arr((1, 0), (1, 1), [$c_3$]),
    )
  ],
  [
    #set align(center)
    #commutative-diagram(
    node-padding: (40pt, 20pt),
      node((0, 0), [$x@0$]),

      node((1, 0), [$y@1$]),

      // node((1, 1), [$not z@1$]),
      // arr((1, 0), (1, 1), [$c_3$]),
    )
  ],
  [
    #set align(center)
    #commutative-diagram(
    node-padding: (40pt, 20pt),
      node((0, 0), [$x@0$]),

      node((1, 0), [$y@1$]),

      node((1, 1), [$not z@1$]),
      arr((1, 0), (1, 1), [$c_3$]),
    )
  ],
)

The core of conflict-driven clause learning (CDCL) is then to define algorithms for finding conflict clauses and backtracking strategies.
