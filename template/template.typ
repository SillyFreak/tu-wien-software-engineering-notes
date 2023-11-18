#let notes(
  title: none,
  subtitle-lines: (),
  authors: (),
  doc,
) = {
  set document(
    title: title
  )

  // title page
  {
    set page(
      paper: "a4",
      margin: (x: 2.8cm, y: 8cm),
    )

    set align(center)
    set heading(outlined: false)

    [
      #set text(size: 16pt)

      = #title

      #v(1cm)

      #for subtitle in subtitle-lines [
        #subtitle
      ]

      #v(3cm)

      #set text(size: 12pt)

      #for author in authors [
        #author
      ]
    ]
  }
  pagebreak()

  set page(
    paper: "a4",
    margin: (x: 2.8cm, y: 2cm),
    numbering: "1/1",
  )

  set heading(numbering: "1.")
  set table(stroke: 0.5pt)

  outline()

  pagebreak()

  doc
}
