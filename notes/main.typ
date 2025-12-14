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
    grid.cell(align: horizon)[(#smallcaps[Var]):],
    one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[Var])],
          $Gamma, x: A tack.r x: A$,
          $Gamma tack.r A "type"$,
        ),
      ),
    )
  ),
)

#show: page
== Derived rules

*Changing and interchanging variables*:

#padded-vertical-grid(
  box(width: 100%)[
    #one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[Rename])],
          $Gamma, x': A, Delta[x' slash x] tack.r cal(J)[x' slash x]$,
          $Gamma, x: A, Delta tack.r cal(J)$,
        ),
      ),
      prooftree(
        rule(
          name: [(#smallcaps[Swap])],
          $Gamma, y: B, x: A, Delta tack.r cal(J)$,
          $Gamma tack.r B "type"$,
          $Gamma, x: A, y: B, Delta tack.r cal(J)$,
        ),
      ),
    )
  ],
)

*Element conversion (#link(<element-conversion-rule-excercise>)[Excercise 1.1.a]) and its congruence (#link(<element-conversion-rule-congruence-excercise>)[Exercise 1.1.b])*:

#padded-vertical-grid(
  box(width: 100%)[
    #one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[ConvElem])],
          $Gamma tack.r a : A'$,
          $Gamma tack.r jteq(A, A')$,
          $Gamma tack.r a : A$,
        ),
      ),
      prooftree(
        rule(
          name: [(#smallcaps[ConvElemCong])],
          $Gamma tack.r a eqdot b : A'$,
          $Gamma tack.r jteq(A, A')$,
          $Gamma tack.r a eqdot b : A$,
        ),
      ),
    )
  ],
)

#show: page
== $Pi$-types

#padded-vertical-grid(
  box(width: 100%)[
    #one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[$Pi$-Form])],
          $Gamma tack.r product_((x: A)) B(x) "type"$,
          $Gamma, x: A tack.r B(x) "type"$,
        ),
      ),
      prooftree(
        rule(
          name: [(#smallcaps[$Pi$-FormCong])],
          $Gamma tack.r product_((x: A)) B(x) eqdot product_((x: A')) B'(x) "type"$,
          $Gamma tack.r jteq(A, A')$,
          $Gamma, x: A tack.r B(x) eqdot B'(x) "type"$,
        ),
      ),
    )
  ],
  box(width: 100%)[
    #one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[$Pi$-Intro])],
          $Gamma tack.r lambda x. b(x): product_((x: A)) B(x)$,
          $Gamma, x: A tack.r b(x): B(x)$,
        ),
      ),
      prooftree(
        rule(
          name: [(#smallcaps[$Pi$-IntroCong])],
          $Gamma tack.r lambda x. b(x) eqdot lambda x. b'(x): product_((x: A)) B(x)$,
          $Gamma, x: A tack.r b(x) eqdot b'(x): B(x)$,
        ),
      ),
    )
  ],
  box(width: 100%)[
    #one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[$Pi$-Elim])],
          $Gamma, x: A tack.r f(x): B(x)$,
          $Gamma tack.r f : product_((x: A)) B(x)$,
        ),
      ),
      prooftree(
        rule(
          name: [(#smallcaps[$Pi$-ElimCong])],
          $Gamma, x: A tack.r f(x) eqdot f'(x): B(x)$,
          $Gamma tack.r f eqdot f' : product_((x: A)) B(x)$,
        ),
      ),
    )
  ],
  box(width: 100%)[
    #one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[$Pi$-Comp / $beta$])],
          $Gamma, x: A tack.r (lambda y. b(y))(x) eqdot b(x): B(x)$,
          $Gamma, x: A tack.r b(x) : B(x)$,
        ),
      ),
      prooftree(
        rule(
          name: [(#smallcaps[$Pi$-Uniq / $eta$])],
          $Gamma tack.r lambda x. f(x) eqdot f : product_((x: A)) B(x)$,
          $Gamma tack.r f : product_((x: A)) B(x)$,
        ),
      ),
    )
  ],
)

== Ordinary function types

#padded-vertical-grid(
  box(width: 100%)[
    #one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[$arrow.r$-Defn])],
          $Gamma tack.r A arrow.r B := product_((x: A)) B "type"$,
          rule(
            $dots.v$,
            $Gamma tack.r A "type"$,
            $Gamma tack.r B "type"$,
          ),
        ),
      ),
    )
  ],
  box(width: 100%)[
    #one-line-grid(
      prooftree(
        rule(
          name: [(#smallcaps[$sans("id")_A$-Defn])],
          $Gamma tack.r sans("id")_A := lambda x. x : A arrow.r A$,
          rule(
            $dots.v$,
            $Gamma tack.r A "type"$,
          ),
        ),
      ),
      prooftree(
        rule(
          name: [(#smallcaps[$sans("comp")$-Defn])],
          $Gamma tack.r sans("comp") := lambda g. lambda f. lambda x. g(f(x)): C^B arrow.r B^A arrow.r C^A$,
          rule(
            $dots.v$,
            $Gamma tack.r A "type"$,
            $Gamma tack.r B "type"$,
            $Gamma tack.r C "type"$,
          ),
        ),
      ),
    )
  ],
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
  ] <element-conversion-rule-excercise>
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
                name: [(#smallcaps[Var])],
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
  ] <element-conversion-rule-congruence-excercise>
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
                name: [(#smallcaps[Var])],
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
== Section 2. Dependent Function Types

=== Exercise 2.1

Give a derivation of the rule

#box(width: 100%)[
  #align(center)[
    #prooftree(
      rule(
        name: [(#smallcaps[FunExt])],
        $Gamma tack.r f eqdot g : product_((x: A)) B(x)$,
        $Gamma tack.r f : product_((x: A)) B(x)$,
        $Gamma tack.r g : product_((x: A)) B(x)$,
        $Gamma, x: A tack.r f(x) eqdot g(x): B(x)$,
      ),
    )
  ]
]

Answer:
#pad(top: 1em, bottom: 1em)[
  #box(width: 100%)[
    #set text(size: 7pt)
    #align(center)[
      #prooftree(
        rule(
          name: [(#smallcaps[JEqEquiv])],
          $Gamma tack.r f eqdot g : product_((x: A)) B(x)$,
          rule(
            name: [(#smallcaps[JEqEquiv])],
            $Gamma tack.r f eqdot lambda x. f(x) : product_((x: A)) B(x)$,
            rule(
              name: [($eta$)],
              $Gamma tack.r lambda x. f(x) eqdot f: product_((x: A)) B(x)$,
              $Gamma tack.r f : product_((x: A)) B(x)$,
            ),
          ),
          rule(
            name: [(#smallcaps[JEqEquiv])],
            $Gamma tack.r lambda x. f(x) eqdot g : product_((x: A)) B(x)$,
            rule(
              name: [(#smallcaps[$Pi$-IntroCong])],
              $Gamma tack.r lambda x. f(x) eqdot lambda x. g(x) : product_((x: A)) B(x)$,
              $Gamma, x: A tack.r f(x) eqdot g(x): B(x)$,
            ),
            rule(
              name: [($eta$)],
              $Gamma tack.r lambda x. g(x) eqdot g: product_((x: A)) B(x)$,
              $Gamma tack.r g : product_((x: A)) B(x)$,
            ),
          ),
        ),
      )
    ]
  ]
]

=== Exercise 2.2

Give a derivation of the rule
#box(width: 100%)[
  #pad(left: 70pt)[
    #prooftree(
      rule(
        name: [($sans(id)$-#smallcaps[RUnit])],
        $Gamma tack.r f compose sans(id)_A eqdot f : A arrow B$,
        $Gamma tack.r f : A arrow B$,
      ),
    )
  ]
]

Answer:

First, we must _assume_ two axioms (which the book does not state explicitly):

#padded-vertical-grid(
  grid(
    columns: (150pt, 2fr, 1fr),
    align: (right, left),
    grid.cell(align: horizon)[(#smallcaps[JEqTyped]):],
    one-line-grid(
      prooftree(
        rule(
          $Gamma tack.r A "type"$,
          $Gamma tack.r A arrow B "type"$,
        ),
      ),
      prooftree(
        rule(
          $Gamma tack.r B "type"$,
          $Gamma tack.r A arrow B "type"$,
        ),
      ),
    )
  ),
)

We have the following lemmas:


#align(left)[
  #box(width: 100%)[
    #lemma[

    ]
  ]
]

#pad(top: 1em, bottom: 2em)[
  #box(width: 100%)[
    #align(center)[
      #set text(size: 3pt)
      #prooftree(
        rule(
          name: [(#smallcaps[FunExt])],
          $Gamma tack.r f compose sans(id)_A eqdot f : A arrow B$,
          rule(
            $Gamma, x: A tack.r (f compose sans("id")_A)(x) eqdot f(x): B$,
            rule(
              name: [(#smallcaps[JEqEquiv])],
              $Gamma, x: A tack.r sans("comp")(f)(sans("id")_A)(x) eqdot f(x): B$,
              rule(
                name: [(#smallcaps[SubstCongr])],
                $Gamma, x: A tack.r sans("comp")(f)(sans("id")_A)(x) eqdot(lambda g. lambda f'. lambda x'. g(f'(x')))(f)(sans("id")_A)(x): B$,
                rule(
                  name: [(#smallcaps[Wk])],
                  $Gamma, x: A tack.r sans("comp") eqdot lambda g. lambda f'. lambda x'. g(f'(x')): B^A arrow (A^A arrow B^A)$,
                  rule(
                    name: [(#smallcaps[$sans("comp")$-Defn])],
                    $Gamma tack.r sans("comp") eqdot lambda g. lambda f'. lambda x'. g(f'(x')): B^A arrow (A^A arrow B^A)$,
                    $Gamma tack.r A "type"$,
                    $Gamma tack.r B "type"$,
                    $Gamma tack.r A "type"$,
                  ),
                ),
                rule(
                  name: [(#smallcaps[JEqEquiv])],
                  $Gamma, x: A, y: B^A arrow (A^A arrow B^A) tack.r y(f)(sans("id")_A)(x) eqdot y(f)(sans("id")_A)(x): B$,
                  rule(
                    name: [(#smallcaps[Swap])],
                    $Gamma, x: A, y: B^A arrow (A^A arrow B^A) tack.r y(f)(sans("id")_A)(x): B$,
                    $Gamma tack.r A "type"$,
                    rule(
                      name: [(#smallcaps[$Pi$-Elim])],
                      $Gamma, y: B^A arrow (A^A arrow B^A), x: A tack.r y(f)(sans("id")_A)(x): B$,
                      rule(
                        name: [(#smallcaps[Subst])],
                        $Gamma, y: B^A arrow (A^A arrow B^A) tack.r y(f)(sans("id")_A): A arrow B$,
                        rule(
                          name: [(#smallcaps[Wk])],
                          $Gamma, y: B^A arrow (A^A arrow B^A) tack.r sans("id")_A: A arrow A$,
                          rule(
                            name: [(#smallcaps[$sans("id")$-Defn])],
                            $Gamma tack.r sans("id")_A: A arrow A$,
                            $Gamma tack.r A "type"$,
                          ),
                        ),
                        rule(
                          name: [(#smallcaps[$Pi$-Elim])],
                          $Gamma, y: B^A arrow (A^A arrow B^A), x: A arrow A tack.r y(f)(x): A arrow B$,
                          rule(
                            name: [(#smallcaps[Subst])],
                            $Gamma, y: B^A arrow (A^A arrow B^A) tack.r y(f): A^A arrow B^A$,
                            rule(
                              name: [(#smallcaps[Wk])],
                              $Gamma, y: B^A arrow (A^A arrow B^A) tack.r f: A arrow B$,
                              $Gamma tack.r f: A arrow B$,
                            ),
                            rule(
                              name: [(#smallcaps[$Pi$-Elim])],
                              $Gamma, y: B^A arrow (A^A arrow B^A), x: B^A tack.r y(x): A^A arrow B^A$,
                              // var
                              $Gamma, y: B^A arrow (A^A arrow B^A) tack.r y: B^A arrow (A^A arrow B^A)$,
                            ),
                          ),
                        ),
                      ),
                    ),
                  ),
                ),
              ),
              rule(
                name: [(#smallcaps[JEqQuiv])],
                $Gamma, x: A tack.r (lambda g. lambda f'. lambda x'. g(f'(x')))(f)(sans("id")_A)(x) eqdot f(x): B$,
                rule(
                  $Gamma, x: A tack.r (lambda g. lambda f'. lambda x'. g(f'(x')))(f)(sans("id")_A)(x) eqdot f(sans("id")_A (x))): B$,
                  rule(
                    name: [(#smallcaps[SubstCongr])],
                    $Gamma, x: A tack.r (lambda g. lambda f'. lambda x'. g(f'(x')))(f)(sans("id")_A)(x) eqdot (lambda f'. lambda x'. f(f'(x')))(sans("id")_A)(x): B$,
                    rule(
                      name: [(#smallcaps[JEqEquiv])],
                      $Gamma, x: A, y: A^A arrow B^A tack.r y(sans("id")_A)(x) eqdot y(sans("id")_A)(x): B$,
                      rule(
                        name: [(#smallcaps[Swap])],
                        $Gamma, x: A, y: A^A arrow B^A tack.r y(sans("id")_A)(x): B$,
                        rule(
                          name: [(#smallcaps[$Pi$-Elim])],
                          $Gamma, y: A^A arrow B^A, x: A tack.r y(sans("id")_A)(x): B$,
                          rule(
                            name: [(#smallcaps[Subst])],
                            $Gamma, y: A^A arrow B^A tack.r y(sans("id")_A): A arrow B$,
                            $Gamma, y: A^A arrow B^A tack.r sans("id")_A : A arrow A$,
                            rule(
                              name: [(#smallcaps[$Pi$-Elim])],
                              $Gamma, y: A^A arrow B^A, x: A^A tack.r y(x): A arrow B$,
                              rule(
                                name: [(#smallcaps[Var])],
                                $Gamma, y: A^A arrow B^A tack.r y: A^A arrow A^B$,
                              ),
                            ),
                          ),
                        ),
                      ),
                    ),
                  ),
                  $Gamma, x: A tack.r (lambda f'. lambda x'. f(f'(x')))(sans("id")_A)(x) eqdot f(sans("id")_A (x))): B$,
                ),
                $Gamma, x: A tack.r f(sans("id")_A (x))) eqdot f(x): B$,
              ),
            ),
          ),
        ),
      )
    ]
  ]
]

#show: page.with(flipped: false)
#bibliography("bibliography.bib")
