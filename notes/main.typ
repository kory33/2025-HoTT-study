#import "@preview/clean-math-paper:0.2.0": *
#import "@preview/curryst:0.5.0": rule, prooftree

#let author = (name: "Ryosuke Kondo", github: "kory33")
#let title = "Study Notes for \n\"Introduction to Homotopy Type Theory\""
#let link-color = rgb("#c20")
#let heading-color = rgb("#007")

// Document's basic properties
#set document(author: author.name, title: title.replace("\n", ""))
#set page(
  margin: (left: 25mm, right: 25mm, top: 25mm, bottom: 30mm),
  numbering: "1",
  number-align: center,
)
#set text(font: "New Computer Modern", lang: "en")
#show link: set text(fill: link-color); #show ref: set text(fill: link-color)
#set heading(numbering: "1.1.1.")
#show heading.where(level: 1): set text(size: 16pt, fill: heading-color)
#show heading.where(level: 2): set text(size: 14pt, fill: heading-color)
#show heading.where(level: 3): set text(size: 12pt, fill: heading-color)

// title page
#pad(bottom: 10%)[
  #align(horizon)[
    #line(length: 100%, stroke: 1pt)
    #pad(bottom: 4pt, top: 4pt, align(center)[#block[#text(weight: 500, 1.75em, title) @rijke2022]])
    #line(length: 100%, stroke: 1pt)

    #v(3em)

    #align(center)[*#author.name* (#author.github)]
    #align(center)[#datetime.today().display("[month repr:long] [day], [year]")]
  ]
]

// preambles
#let eqdot = context {
  let eq = $=$
  let dot = $.$
  let cancel-width = (measure(eq).width + measure(dot).width) / 2

  $#eq#h(-cancel-width);#box(baseline: -0.47em)[#dot]#h(cancel-width)$
}
#let jteq(l, r) = $#l eqdot #r "type"$

// Main body
#show: page
#set text(size: 10pt)

= Rules Cheatsheet
== Inference rules for MLTT

#let one-line-grid(..row) = {
  [
    #align(center)[
      #grid(
        columns: row.pos().len(), rows: 1, column-gutter: 4%,
        ..row
      )
    ]
  ]
}
#let padded-vertical-grid(..rows) = {
  pad(top: 1em, bottom: 2em)[
    #grid(
      columns: 1, row-gutter: 2em,
      ..rows
    )
  ]
}

#v(1em)
*Rules about the formation of contexts, types, and their elements*:

#padded-vertical-grid(
  grid(
    columns: (80pt, 1fr),
    align: (right, left),
    grid.cell(align: horizon)[(#smallcaps[Wf]):],
    one-line-grid(
      prooftree(rule($Gamma tack.r A "type"$, $Gamma, x: A tack.r B(x) "type"$)),
      prooftree(rule($Gamma tack.r A "type"$, $Gamma tack.r a: A$)),
      prooftree(rule($Gamma tack.r A "type"$, $Gamma tack.r jteq(A, B)$)),
      prooftree(rule($Gamma tack.r B "type"$, $Gamma tack.r jteq(A, B)$)),
    )
  ),
  grid(
    columns: (80pt, 1fr),
    align: (right, left),
    grid.cell(align: horizon)[(#smallcaps[JEqTyped]):],
    one-line-grid(
      prooftree(rule($Gamma tack.r a: A$, $Gamma tack.r a eqdot b : A$)),
      prooftree(rule($Gamma tack.r b: A$, $Gamma tack.r a eqdot b : A$)),
    )
  ),
)

*Judgmental (term / type) equality is an equivalence relation*:

#padded-vertical-grid(
  grid(
    columns: (80pt, 1fr),
    align: (right, left),
    grid.cell(align: horizon)[(#smallcaps[JTEqEquiv]):],
    one-line-grid(
      prooftree(rule($Gamma tack.r jteq(A, A)$, $Gamma tack.r A "type"$)),
      prooftree(rule($Gamma tack.r jteq(B, A)$, $Gamma tack.r jteq(A, B)$)),
      prooftree(
        rule(
          $Gamma tack.r jteq(A, C)$,
          $Gamma tack.r jteq(A, B)$,
          $Gamma tack.r jteq(B, C)$,
        ),
      ),
    )
  ),
  grid(
    columns: (80pt, 1fr),
    align: (right, left),
    grid.cell(align: horizon)[(#smallcaps[JEqEquiv]):],
    one-line-grid(
      prooftree(rule($Gamma tack.r a eqdot a : A$, $Gamma tack.r a: A$)),
      prooftree(rule($Gamma tack.r b eqdot a : A$, $Gamma tack.r a eqdot b : A$)),
      prooftree(rule($Gamma tack.r a eqdot c : A$, $Gamma tack.r a eqdot b : A$, $Gamma tack.r b eqdot c : A$)),
    )
  ),
)

*Variable conversion and substitution*:

#padded-vertical-grid(
  grid(
    columns: (80pt, 1fr),
    align: (right, left),
    grid.cell(align: horizon)[(#smallcaps[ConvVar]):],
    one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[ConvVar])],
          $Gamma, x: A', Delta tack.r cal(J)$,
          $Gamma tack.r A eqdot A' "type"$,
          $Gamma, x: A, Delta tack.r cal(J)$,
        ),
      ),
    )
  ),
  grid(
    columns: (80pt, 1fr),
    align: (right, left),
    grid.cell(align: horizon)[(#smallcaps[Subst]):],
    one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[Subst])],
          $Gamma, Delta[a slash x] tack.r cal(J)[a slash x]$,
          $Gamma tack.r a: A$,
          $Gamma, x: A, Delta tack.r cal(J)$,
        ),
      ),
    )
  ),
  grid(
    columns: (80pt, 1fr),
    align: (right, left),
    grid.cell(align: horizon)[(#smallcaps[SubstCongr]):],
    one-line-grid(
      prooftree(
        rule(
          $Gamma, Delta[a slash x] tack.r B[a slash x] eqdot B[a' slash x] "type"$,
          $Gamma tack.r a eqdot a' : A$,
          $Gamma, x: A, Delta tack.r B "type"$,
        ),
      ),
      prooftree(
        rule(
          $Gamma, Delta[a slash x] tack.r b[a slash x] eqdot b[a' slash x]: B[a slash x]$,
          $Gamma tack.r a eqdot a' : A$,
          $Gamma, x: A, Delta tack.r b: B$,
        ),
      ),
    )
  ),
)

*Weakening*:

#padded-vertical-grid(
  grid(
    columns: (80pt, 1fr),
    align: (right, left),
    grid.cell(align: horizon)[(#smallcaps[Wk]):],
    one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[Wk])],
          $Gamma, x: A, Delta tack.r cal(J)$,
          $Gamma tack.r A "type"$,
          $Gamma, Delta tack.r cal(J)$,
        ),
      ),
    )
  ),
)

*Generic elements*:

#padded-vertical-grid(
  grid(
    columns: (80pt, 1fr),
    align: (right, left),
    grid.cell(align: horizon)[($delta$):],
    one-line-grid(
      prooftree(
        rule(
          name: [($delta$)],
          $Gamma, x: A tack.r x: A$,
          $Gamma tack.r A "type"$,
        ),
      ),
    )
  ),
)

#show: page
= Answers to Exercises
== Section 1. Dependent Type Theory
=== Excercise 1.1

- #box(width: 100%)[
    (a). Give a derivation for the following *element conversion rule*:
    $
      #prooftree(rule(
        name: [(#smallcaps[ConvElem])],
        $Gamma tack.r a : A'$,
        $Gamma tack.r jteq(A, A')$,
        $Gamma tack.r a : A$,
      ))
    $
  ]
  - Answer:
    #pad(top: 1em, bottom: 2em)[
      #box(width: 100%)[
        $
          #prooftree(
          rule(
            name: [(#smallcaps[Subst])],
            $Gamma tack.r a : A'$,
            $Gamma tack.r a : A$,
            rule(
              name: [(#smallcaps[ConvVar])],
              $Gamma, x : A tack.r x : A'$,
              rule(
                name: [(#smallcaps[JTEqEquiv])],
                $Gamma tack.r jteq(A', A)$,
                $Gamma tack.r jteq(A, A')$,
              ),
              rule(
                name: [($delta$)],
                $Gamma, x : A' tack.r x : A'$,
                rule(
                  name: [(#smallcaps[Wf])],
                  $Gamma tack.r A' "type"$,
                  $Gamma tack.r jteq(A, A')$,
                ),
              ),
            )
          )
        )
        $
      ]
    ]
- #box(width: 100%)[
    (b). Give a derivation for the following *congruence rule* for element conversion:
    $
      #prooftree(rule(
        name: [(#smallcaps[ConvElem])],
        $Gamma tack.r a eqdot b : A'$,
        $Gamma tack.r jteq(A, A')$,
        $Gamma tack.r a eqdot b : A$,
      ))
    $
  ]
  - Answer:
    #pad(top: 1em, bottom: 2em)[
      #box(width: 100%)[
        $
          #prooftree(
          rule(
            name: [(#smallcaps[SubstCongr])],
            $Gamma tack.r a eqdot b : A'$,
            $Gamma tack.r a eqdot b : A$,
            rule(
              name: [(#smallcaps[ConvVar])],
              $Gamma, x : A tack.r x : A'$,
              rule(
                name: [(#smallcaps[JTEqEquiv])],
                $Gamma tack.r jteq(A', A)$,
                $Gamma tack.r jteq(A, A')$,
              ),
              rule(
                name: [($delta$)],
                $Gamma, x : A' tack.r x : A'$,
                rule(
                  name: [(#smallcaps[Wf])],
                  $Gamma tack.r A' "type"$,
                  $Gamma tack.r jteq(A, A')$,
                ),
              ),
            )
          )
        )
        $
      ]
    ]

#show: page
#bibliography("bibliography.bib")
