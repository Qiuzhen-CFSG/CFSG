module

public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# Centralizer supplements for extraspecial normal subgroups

If an ambient group acts trivially on P/Z(P), each induced automorphism
of the extraspecial group P is inner. Multiplying an ambient element by
the inverse of its inner representative in P gives an element of C_L(P)
with the same image in L/P. Thus the actual centralizer projects onto L/P.

This handles the trivial-action case of Aschbacher--Smith,
*The Classification of Quasithin Groups*, A.1.33(2), printed p.29.
-/

open Subgroup
namespace IsExtraspecial
variable {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]

/-- Innerness of the action supplies a representative in the centralizer
for every coset of the normal extraspecial subgroup. -/
public theorem centralizer_projection_surjective_of_trivial_quotient_action
    (P : Subgroup L) [P.Normal] [IsExtraspecial p P]
    (htriv : ∀ x : L, quotientAut (center P) (MulAut.conjNormal x) = 1) :
    Function.Surjective ((QuotientGroup.mk' P).comp
      (centralizer (P : Set L)).subtype) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P q
  have hx : (MulAut.conjNormal x : MulAut P) ∈ (MulAut.conj : P →* MulAut P).range := by
    rw [← IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := p)]
    exact htriv x
  obtain ⟨y, hy⟩ := hx
  have hyconj : (MulAut.conjNormal (y : L) : MulAut P) = MulAut.conjNormal x := by
    rw [MulAut.conjNormal_val]
    exact hy
  have hyx : (MulAut.conjNormal ((y : L)⁻¹ * x) : MulAut P) = 1 := by
    rw [map_mul, map_inv, hyconj, inv_mul_cancel]
  have hcentral : (y : L)⁻¹ * x ∈ centralizer (P : Set L) := by
    intro z hz
    have heq := congrArg Subtype.val (DFunLike.congr_fun hyx (⟨z, hz⟩ : P))
    rw [MulAut.conjNormal_apply] at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  refine ⟨⟨_, hcentral⟩, ?_⟩
  change QuotientGroup.mk' P ((y : L)⁻¹ * x) = QuotientGroup.mk' P x
  have hyq : QuotientGroup.mk' P (y : L) = 1 :=
    (QuotientGroup.eq_one_iff (y : L)).mpr y.property
  rw [map_mul, map_inv, hyq, inv_one, one_mul]

end IsExtraspecial
