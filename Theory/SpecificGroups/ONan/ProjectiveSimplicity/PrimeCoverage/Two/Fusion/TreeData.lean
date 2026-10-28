module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.FusionReduction

/-!
# Numerical data for the O'Nan involution fusion certificate

Transcribed from `Two/source/discovery.json`, generated from the preserved
ATLAS matrices by `Two/source/Generate.py`. These are only numerical data;
word evaluations and every matrix identity require separate Lean proofs.
The original matrices and attribution to R. A. Wilson, R. A. Parker,
J. N. Bray and the ATLAS contributors are preserved in `refs/original/onan/`.
-/

namespace ONan.Simplicity.TwoCertificate.Fusion

/-- Indices of the candidate involutions, in tree order. -/
@[expose] public def vertex : Fin 87 → Fin 512 :=
  ![2, 280, 450, 202, 402, 154, 266, 346, 136, 464, 216, 82, 384, 64, 16, 328, 4, 128, 452, 108, 268, 356, 204, 164, 428, 24, 32, 320, 184, 472, 480, 376, 5, 129, 143, 33, 91, 321, 459, 165, 357, 287, 453, 315, 209, 11, 127, 171, 495, 47, 223, 85, 411, 335, 447, 481, 251, 363, 113, 245, 309, 405, 273, 433, 8, 430, 256, 96, 456, 416, 110, 206, 310, 406, 246, 86, 168, 192, 360, 270, 56, 424, 504, 104, 80, 400, 448]

/-- The parent of each vertex; roots are their own parents. -/
@[expose] public def parent : Fin 87 → Fin 87 :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 3, 6, 7, 8, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 19, 22, 23, 24, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 37, 37, 38, 39, 40, 40, 43, 43, 44, 44, 45, 49, 64, 64, 64, 64, 64, 65, 65, 65, 65, 65, 65, 65, 66, 66, 69, 70, 80, 80, 80, 81, 84, 84, 86]

/-- The basis letter conjugating the parent to this child. -/
@[expose] public def label : Fin 87 → Fin 9 :=
  ![0, 0, 2, 3, 4, 5, 8, 0, 1, 2, 3, 4, 0, 0, 0, 4, 0, 0, 1, 3, 4, 5, 6, 7, 8, 1, 2, 4, 0, 0, 0, 0, 0, 0, 1, 2, 3, 5, 8, 0, 2, 3, 5, 2, 3, 5, 3, 4, 8, 2, 5, 8, 1, 8, 2, 0, 3, 8, 4, 8, 2, 5, 1, 3, 0, 0, 1, 2, 5, 0, 2, 3, 4, 5, 6, 7, 2, 3, 1, 3, 0, 0, 1, 1, 0, 0, 0]

/-- The seven root vertices. -/
@[expose] public def root : Fin 7 → Fin 87 :=
  ![0, 16, 32, 64, 80, 84, 86]

/-- Ambient words for the seven odd-product witnesses. -/
@[expose] public def rootWord : Fin 7 → List (Fin 2) :=
  ![[1], [], [1], [1, 0, 1], [0, 1], [], [1]]

/-- The odd exponent is twice this number plus one. -/
@[expose] public def rootHalfExponent : Fin 7 → ℕ :=
  ![9, 9, 9, 9, 7, 7, 5]

/-- Every nonroot vertex has an earlier parent. This checks only finite data. -/
public theorem root_or_parent_lt (t : Fin 87) :
    (∃ r : Fin 7, t = root r) ∨ parent t < t := by
  have h : ∀ t : Fin 87, (∃ r : Fin 7, t = root r) ∨ parent t < t := by
    decide +kernel
  exact h t

end ONan.Simplicity.TwoCertificate.Fusion
