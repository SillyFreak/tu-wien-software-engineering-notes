#import "@preview/commute:0.2.0": node, arr, commutative-diagram

#let Carrier = $cal(C)$
#let Lattice(carrier) = $accent(carrier, hat)$
// TODO manual kerning for calligraphy letters
#let FL = $cal("F")#h(-0.22em)cal("L")$

#let rel = $subset.eq.sq$

#let meet = $sect.sq$
#let Meet = $sect.sq.big$
#let join = $union.sq$
#let Join = $union.sq.big$

$
Lattice(Carrier) = (Carrier, rel, meet, join, bot, top) \

Meet {c_1, ..., c_k} = c_1 meet ... meet c_k \

Join {c_1, ..., c_k} = c_1 join ... join c_k
$

#let hasse-boolean = commutative-diagram(
  node-padding: (28pt, 28pt),
  // arr-clearance: 1em,
  node((0, 0), [$t$]),
  node((1, 0), [$f$]),
  arr((1, 0), (0, 0), []),
)

#figure(
  caption: [Hasse diagram of $Lattice(BB)$],
  hasse-boolean
)

#let hasse-boolean-inv = commutative-diagram(
  node-padding: (28pt, 28pt),
  // arr-clearance: 1em,
  node((0, 0), [$f$]),
  node((1, 0), [$t$]),
  arr((1, 0), (0, 0), []),
)

#figure(
  caption: [Hasse diagram of $Lattice(BB_or)$],
  hasse-boolean-inv
)

#let hasse-flat-boolean = commutative-diagram(
  node-padding: (28pt, 28pt),
  arr-clearance: 1em,
  node((0, 1), [$top$]),
  node((1, 0), [$f$]),
  node((1, 2), [$t$]),
  node((2, 1), [$bot$]),
  arr((2, 1), (1, 0), []),
  arr((2, 1), (1, 2), []),
  arr((1, 0), (0, 1), []),
  arr((1, 2), (0, 1), []),
)

#figure(
  caption: [Hasse diagram of $FL_BB$],
  hasse-flat-boolean
)

#let hasse-flat-integers(breadth) = {
  let min = -breadth
  let count = breadth*2 + 1
  let middle = breadth + 1
  let right = count + 1

  commutative-diagram(
    node-padding: (20pt, 28pt),
    // arr-clearance: 0.5em,
    node((0, middle), [$top$]),
    node((1, 0), [$...$]),
    ..range(0, count).map((i) => (
      node((1, i+1), [$#(min + i)$]),
      arr((1, i+1), (0, middle), []),
      arr((2, middle), (1, i+1), []),
    )).flatten(),
    node((1, right), [$...$]),
    node((2, middle), [$bot$]),
  )
}

#figure(
  caption: [Hasse diagram of $FL_ZZ$],
  hasse-flat-integers(2)
)

#figure(
  caption: [Hasse diagram of $FL_ZZ$],
  hasse-flat-integers(3)
)
