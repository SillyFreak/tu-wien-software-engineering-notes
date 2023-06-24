// lattices
#let Carrier = $cal(C)$
#let Lattice(carrier) = $accent(carrier, hat)$
// TODO manual kerning for calligraphy letters
#let FL = $cal("F")#h(-0.22em)cal("L")$

#let rel = $subset.eq.sq$

#let meet = $sect.sq$
#let Meet = $sect.sq.big$
#let join = $union.sq$
#let Join = $union.sq.big$

// flow graphs
#let instr = $dotless.i$
#let skip = $upright("skip")$
#let succ = $italic("succ")$
#let pred = $italic("pred")$

// DFAs
#let Spec = $cal(S)$
#let Func(e: $thick$) = $bracket.l.double #e bracket.r.double$
#let fw = $italic("fw")$
#let bw = $italic("bw")$

#let Const = $italic("Cst")$
#let Id = $italic("Id")$

#let Vars = $upright(bold("V"))$
#let Consts = $upright(bold("C"))$
#let Terms = $upright(bold("T"))$
#let Ops = $upright(bold("O"))$
#let Eval = $cal(E)$

#let path(body) = $angle.l body angle.r$

#let Paths = $upright(bold("P"))$
#let CM = $italic("CM")$
#let BCM = $italic("BCM")$
#let LCM = $italic("LCM")$
#let SpCM = $italic("SpCM")$
#let Insert = $italic("Insert")$
#let Repl = $italic("Repl")$
#let Comp = $italic("Comp")$
#let Transp = $italic("Transp")$
#let Safe = $italic("Safe")$
#let Correct = $italic("Correct")$
#let Available = $italic("Available")$
#let VeryBusy = $italic("VeryBusy")$
#let Earliest = $italic("Earliest")$
