module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.FourSpace

/-!
# An explicit five-involution comparison for the binary middle Levi

The five displayed words in the four signed middle-root generators restrict to
an A₅ Coxeter chain on the four half-root lines. Their ambient evaluations are
involutions and intertwine with their four-dimensional evaluations. The two
short-root recovery words and the ambient Coxeter relations are separate
obligations; these definitions do not assume either one.

This is a finite presentation route to faithfulness of the split B₂ Levi in
Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 (PDF pp.274–275) of
`refs/quasithin.pdf`. The ambient action is the integral Geck construction.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof

/-- Five words proposed as an A₅ chain of involutions. -/
def chainWord (i : Fin 5) : List (Fin 4) :=
  ![[0], [2], [1, 0, 1], [1, 3, 2, 3, 1], [3, 1, 0, 1, 3]] i

/-- Words in the chain recovering the long+, short+, long−, short− generators. -/
def recoveryWord (i : Fin 4) : List (Fin 5) :=
  ![[0], [0, 1, 0, 2, 1, 0, 4], [1], [0, 2, 3, 2, 4, 3, 2]] i

/-- Evaluate the five words in the actual F₄ Levi. -/
def ambientChain (i : Fin 5) : splitLevi :=
  ((chainWord i).map splitGenerator).prod

/-- Evaluate the same five words in the four-dimensional matrices. -/
def fourChain (i : Fin 5) : BinaryGL :=
  ((chainWord i).map matrixGenerator).prod

theorem splitGenerator_inv (i : Fin 4) : (splitGenerator i)⁻¹ = splitGenerator i := by
  apply ambientLeviHom_injective
  change (Theory.AlgebraicGroup.F4Chevalley.rootCurve (signedRoot i)
    (1 : CoefficientField 0))⁻¹ = _
  rw [Theory.AlgebraicGroup.F4Chevalley.rootCurve_inv, CharTwo.neg_eq]
  rfl

theorem ambientChain_inv (i : Fin 5) : (ambientChain i)⁻¹ = ambientChain i := by
  fin_cases i <;>
    simp [ambientChain, chainWord, mul_inv_rev, splitGenerator_inv, mul_assoc]

/-- Each proposed ambient simple reflection is already a proved involution. -/
theorem ambientChain_sq (i : Fin 5) : ambientChain i * ambientChain i = 1 := by
  simpa only [ambientChain_inv] using inv_mul_cancel (ambientChain i)

/-- The intertwining calculation extends to every positive generator word. -/
theorem word_intertwines (w : List (Fin 4)) :
    (ambientLeviHom ((w.map splitGenerator).prod)).val * fourEmbedding =
      fourEmbedding * ((w.map matrixGenerator).prod).val := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Units.val_mul]
    rw [Matrix.mul_assoc, ih, ← Matrix.mul_assoc, splitGenerator_intertwines,
      Matrix.mul_assoc]

theorem ambientChain_intertwines (i : Fin 5) :
    (ambientLeviHom (ambientChain i)).val * fourEmbedding =
      fourEmbedding * (fourChain i).val := word_intertwines _

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof
