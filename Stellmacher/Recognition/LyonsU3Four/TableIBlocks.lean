module

public import Stellmacher.Recognition.LyonsU3Four.TableIPatterns

/-!
# The shared blocks of Lyons's Table I

The seven blocks Z₁–Z₇ are transcribed in printed row and column order.
The columns are `dᵗ, ₁dᶻ, ₂dᶻ, ₃dᶻ, ₄dᶻ, ₅dᶻ`. Row repetitions in the
assembled matrices are retained by using finite indexed functions.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), Table I, p. 377. Checked against the page image in
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
namespace TableICatalogue

/-- The printed block Z1. -/
def z1 : TableIMatrix (Fin 6) := ![
  ![1, 1, 0, 0, 0, 0],
  ![-1, 1, 1, 1, 1, -1],
  ![-1, 1, 1, 1, -1, 1],
  ![-1, 1, 1, -1, 1, 1],
  ![-1, 1, -1, 1, 1, 1],
  ![-2, 2, 2, 2, 2, 2]]

/-- The printed block Z2. -/
def z2 : TableIMatrix (Fin 6) := ![
  ![1, 1, 0, 0, 0, 0],
  ![-1, 1, 0, 0, 0, 2],
  ![-1, 1, 0, 0, 2, 0],
  ![-1, 1, 0, 2, 0, 0],
  ![-1, 1, 2, 0, 0, 0],
  ![-2, 2, 2, 2, 2, 2]]

/-- The printed block Z3. -/
def z3 : TableIMatrix (Fin 10) := ![
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 2, 0, 1, 1],
  ![1, 1, 0, 1, 1, 2],
  ![1, 1, 1, 1, 2, 0],
  ![1, 1, 1, 2, 0, 1],
  ![-1, 1, 1, 1, 0, 0],
  ![-1, 1, 1, 0, 0, 1],
  ![-1, 1, 0, 0, 1, 1],
  ![-1, 1, 0, 1, 1, 0],
  ![-2, 2, 2, 2, 2, 2]]

/-- The printed block Z4. -/
def z4 : TableIMatrix (Fin 5) := ![
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 2, 1, 0, 1],
  ![1, 1, 1, 0, 1, 2],
  ![1, 1, 0, 1, 2, 1],
  ![1, 1, 1, 2, 1, 0]]

/-- The printed block Z5. -/
def z5 : TableIMatrix (Fin 4) := ![
  ![1, 0, 1, 0, 0, 0],
  ![1, 0, 0, 1, 0, 0],
  ![1, 0, 0, 0, 1, 0],
  ![1, 0, 0, 0, 0, 1]]

/-- The printed block Z6. -/
def z6 : TableIMatrix (Fin 4) := ![
  ![0, 1, 1, 1, 1, 0],
  ![0, 1, 1, 1, 0, 1],
  ![0, 1, 1, 0, 1, 1],
  ![0, 1, 0, 1, 1, 1]]

/-- The printed block Z7. -/
def z7 : TableIMatrix (Fin 5) := ![
  ![1, 1, 0, 0, 0, 0],
  ![-1, 1, 1, 1, 0, 0],
  ![-1, 1, 1, 0, 0, 1],
  ![-1, 1, 0, 0, 1, 1],
  ![-1, 1, 0, 1, 1, 0]]

/-- The two alternatives for the initial six rows of A–E. -/
inductive ZChoice where
  | z1 | z2
  deriving DecidableEq, Repr

/-- The selected six-row block, including the principal row. -/
def initial : ZChoice → TableIMatrix (Fin 6)
  | .z1 => z1
  | .z2 => z2

end TableICatalogue
end Stellmacher.Recognition.LyonsU3Four
