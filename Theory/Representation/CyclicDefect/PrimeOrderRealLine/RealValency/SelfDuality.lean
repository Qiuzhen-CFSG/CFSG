module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SelfDuality.Dual
public import Theory.Character.ClassSumFormula

/-!
# Real ordinary characters force conjugacy to inverses

A complete family of ordinary irreducible characters spans all complex
class functions, so it separates conjugacy classes. When every row is real,
the character identity at inverses makes the classes of `g` and `g⁻¹` equal.
Together with `equiv_dual_of_isConj_inv`, this gives actual self-duality of
irreducibles over any algebraically closed field, including modular fields.

This is the route used for the supplied principal eleven-block edge modules
in the real-valency argument of Feit VII.2.24 (proof p.303) and VII.9.2
(p.307). It uses the complete ordinary family, not merely the block rows.
-/

public section

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency

/-- A complete ordinary irreducible character family separates actual
conjugacy classes. -/
theorem completeFamily_separates
    {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    {χ : ι → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ)
    {x y : ConjClasses G} (hxy : ∀ i, χ i x = χ i y) : x = y := by
  classical
  have hφ (φ : ConjClassFunction G) : φ x = φ y := by
    rw [completeFamily_apply_eq_sum_inner hχ φ x, completeFamily_apply_eq_sum_inner hχ φ y]
    simp_rw [hxy]
  by_contra hne
  have h := hφ (fun c => if c = x then 1 else 0)
  simp [Ne.symm hne] at h

/-- Realness of every ordinary irreducible implies that each group element
is conjugate to its inverse. -/
theorem isConj_inv_of_real_completeFamily
    {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    {χ : ι → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (hreal : ∀ i c, star (χ i c) = χ i c) (g : G) : IsConj g g⁻¹ := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mp
  apply completeFamily_separates hχ
  intro i
  rw [← Theory.Character.star_conjChar_apply_inv (hχ.1 i).1 g, hreal]

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency
