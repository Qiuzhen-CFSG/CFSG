module

public import Theory.SpecificGroups.SU3.CyclicCoreSylow.Generators
public import Theory.SpecificGroups.SU3.CyclicCoreSylow.Order
public import Theory.SpecificGroups.SU3.CyclicCoreSylow.Extension

/-!
# Cyclic coordinates in a full automorphism Sylow of PSU₃(p)

For p prime and congruent to one modulo four, a Sylow two-subgroup of the
full automorphism group of the actual projective special unitary model
has the cyclic-by-four coordinates. Its inner rotation and swap come from
the hyperbolic matrix block; its outer involution is entrywise Frobenius.
The cubic scalar kernel preserves the rotation order, the projective order
formula proves inner Sylow maximality, and semilinear coverage accounts
for all full-automorphism actors, including the odd diagonal quotient.

Simplicity is inherited, as in the source application. No model isomorphism,
Sylow shape, automorphism-order formula or coordinate hypothesis remains.

Source: Aschbacher–Smith E.1.14(7), printed p.214, citing Aschbacher (1982),
Lemma 4.11; A.3.21(b), printed p.55; ABG II.2 Lemma 1, article p.17.
-/

public section
open Matrix Subgroup Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.CyclicCoreSylow

/-- The full automorphism Sylow, literal inner subgroup and actual marked
projective involution, with all cyclic-coordinate relations proved. -/
theorem exists_cyclicByFour_sylow
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    ∃ (S : Sylow 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
      (w : ProjectiveSpecialUnitaryMatrixGroup J),
      orderOf w = 2 ∧ Nonempty (CyclicByFourCoordinates
        (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        (S : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (MulAut.conj w)) := by
  obtain ⟨n, hdiv, hodd⟩ := exists_parameter hp hmod
  obtain ⟨x, y, hx, hy, hyx, hγx, hγy⟩ := exists_generators J hJ hp ho hcard hc n hdiv hodd
  exact exists_full_sylow_of_generators J hJ hp ho hcard hc n x y hx hy hyx
    (OddPrimeSylow.NormalizedOuter.entrywiseProjectiveAut J hJ)
    (OddPrimeSylow.NormalizedOuter.entrywiseProjectiveAut_isEntrywiseConjugation J hJ)
    hγx hγy (two_subgroup_card_le J hJ hp ho hcard hc n hdiv hodd)

end BenderSuzuki.MatrixGroups.HermitianForm.CyclicCoreSylow
