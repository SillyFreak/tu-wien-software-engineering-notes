#import "@preview/commute:0.2.0": node, arr, commutative-diagram

#let empty = $$
#let skip = $upright("skip")$
#let assign(v, t) = $#v := #t$

#let stmt-node(..args) = {
  rect(
    width: 5em,
    stroke: 0.5pt,
    // if no args are given, make sure that we include the empty statement so that there's content setting the rect's height
    ..if args.pos().len() == 0 { (empty,) },
    ..args,
  )
}

#let edge(a, b, nodes: none, start-space: none, end-space: none, label-pos: 1em, curve: 0deg, stroke: 0.45pt, ..options) = {
  assert(nodes != none)

  arr(
    nodes.at(a).at(0),
    nodes.at(b).at(0),
    [],
    start-space: start-space,
    end-space: end-space,
    label-pos: label-pos,
    curve: curve,
    stroke: stroke,
    ..options
  )
}

#let edges(nodes: none, edge: edge, ..names) = {
  assert(nodes != none)

  names = names.pos()
  range(names.len() - 1).map((i) => {
    let a = names.at(i)
    let b = names.at(i+1)

    edge(a, b, nodes: nodes)
  })
}

#let node-labelled-graph(nodes: none, ..options) = {
  assert(nodes != none)

  commutative-diagram(
    node-padding: (-10pt, 20pt),
    arr-clearance: 0.2em,
    ..nodes.values().map(((pos, body)) => node(pos, body)),
    ..options,
  )
}

#figure(caption: [node-labelled flow graph])[
  #let node = stmt-node

  #let nodes = (
    // put something in column 3 so that spacing is correct
    "dummy": ((0, 3), node(stroke: none)),
    "1": ((0, 1), node()),
    "2": ((1, 0), node($assign(a, c)$)),
    "3": ((2, 0), node($assign(x, a+b)$)),
    "4": ((2, 2), node()),
    "5": ((2, 4), node($assign(y, a+b)$)),
    "6": ((3, 1), node()),
  )

  #let edge = edge.with(nodes: nodes)
  #let edges = edges.with(nodes: nodes)

  #node-labelled-graph(
    nodes: nodes,
    ..edges("1", "2", "3", "6"),
    ..edges("1", "4", "6"),
    edge("4", "5", curve: -40deg),
    edge("5", "4", curve: -40deg),
  )
]

#let circ-node = circle.with(
  radius: 1em,
  stroke: 0.5pt,
)

#let stmt-edge(a, b, stmt, nodes: none, ..options) = {
  assert(nodes != none)

  arr(
    nodes.at(a).at(0),
    nodes.at(b).at(0),
    stmt,
    ..options
  )
}

#let stmt-edges(nodes: none, edge: stmt-edge, ..namesAndStmts) = {
  assert(nodes != none)
  namesAndStmts = namesAndStmts.pos()
  assert(calc.rem(namesAndStmts.len(), 2) == 1)

  range(namesAndStmts.len() - 1, step: 2).map((i) => {
    let a = namesAndStmts.at(i)
    let stmt = namesAndStmts.at(i+1)
    let b = namesAndStmts.at(i+2)

    edge(a, b, stmt, nodes: nodes)
  })
}

#let edge-labelled-graph(nodes: none, ..options) = {
  assert(nodes != none)

  commutative-diagram(
    node-padding: (20pt, 20pt),
    arr-clearance: 0.2em,
    ..nodes.values().map(((pos, body)) => node(pos, body)),
    ..options,
  )
}

#figure(caption: [edge-labelled flow graph])[
  #let node = circ-node

  #let nodes = (
    // put something in column 3 so that spacing is correct
    "1": ((0, 1), node()),
    "3": ((1, 0), node()),
    "4": ((1, 2), node()),
    "5": ((1, 4), node()),
    "6": ((2, 1), node()),
  )

  #let edge = stmt-edge.with(nodes: nodes)
  #let edges = stmt-edges.with(nodes: nodes)

  #edge-labelled-graph(
    nodes: nodes,
    ..edges(
      "1",
      $assign(a, c)$,
      "3",
      $assign(x, a+b)$,
      "6",
    ),
    ..edges(
      "1",
      empty,
      "4",
      empty,
      "6",
      ),
    edge("4", "5", $assign(y, a+b)$, curve: -40deg),
    edge("5", "4", empty, curve: -40deg),
  )
]
