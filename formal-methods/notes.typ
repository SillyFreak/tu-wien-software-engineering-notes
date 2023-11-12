#import "@preview/cetz:0.1.2": canvas, draw, tree

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
