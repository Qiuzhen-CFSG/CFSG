module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFourParabolicCardinality

/-!
# The full PSU₅(4) parabolics for the quasithin converse

For the identity Hermitian form over any field of order sixteen with
fourth-power conjugation, the actual projective line and plane stabilizers
have the stated orders. Their concrete matrix unipotent subgroups are normal
inside the respective full stabilizers. The proofs use the exhaustive line
block decomposition and the exact plane restriction quotient, including the
projective scalar kernels.

These are the order and relative-normality inputs to the PSU₅(4) converse;
rank bounds and identification of the two-cores belong to its assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1) and F.1.12(7), printed pp.4 and 263--264.
-/

public section

namespace CFSG.Quasithin.MainConverse.UnitaryFive
open BenderSuzuki.MatrixGroups Theory.SpecificGroups.UnitaryFive
variable {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)

/-- The full projective line stabilizer, including its cubic Levi factor. -/
theorem card_lineParabolic (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    Nat.card (lineParabolic J) = 2 ^ 20 * (3 ^ 2 * 5 ^ 2 * 13) :=
  card_lineParabolic_four J hcard hconj hJ

/-- The full projective plane stabilizer, with Levi GL₂(F)/C₅. -/
theorem card_planeParabolic (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    Nat.card (planeParabolic J) = 2 ^ 20 * (3 ^ 2 * 5 * 17) :=
  card_planeParabolic_four J hcard hconj hJ

/-- Relative normality in the entire line parabolic. -/
theorem line_projectiveUnipotent_normal (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    (LineCore.Parabolic.projectiveUnipotent J hJ).Normal :=
  line_projectiveUnipotent_normal_four J hcard hconj hJ

omit [Finite F] in
/-- Relative normality in the entire plane parabolic. -/
theorem plane_projectiveUnipotent_normal (hJ : J.form = 1) :
    (PlaneCore.projectiveUnipotent J hJ).Normal :=
  PlaneCore.projectiveUnipotent_normal J hJ

end CFSG.Quasithin.MainConverse.UnitaryFive
