module

public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Sylow-central elements in a faithful normal subgroup

If every pointwise fixer of a Sylow subgroup of L is inner, an ambient element
centralizing a Sylow subgroup belongs to L, provided C_G(L) is trivial.
Restrict the Sylow subgroup to the normal subgroup L, apply the fixer theorem,
and use the faithful conjugation action to identify the actual element.

This retains relative normality and the original Sylow subgroup. It is the
inner-marking step used in Aschbacher–Smith, 13.5.21(i), printed pp.923–924.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Pointwise innerness on the normal subgroup identifies the actual ambient
Sylow-central element, rather than only its induced automorphism. -/
theorem mem_normal_of_centralizes_sylow
    (L : Subgroup G) [L.Normal]
    (hfaith : centralizer (L : Set G) = ⊥)
    (hinner : ∀ (P : Sylow 2 L) (a : MulAut L),
      (∀ x ∈ P, a x = x) → ∃ z ∈ P, a = MulAut.conj z)
    (S : Sylow 2 G) (v : G)
    (hc : ∀ x ∈ S, x * v = v * x) : v ∈ L := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal L
  obtain ⟨z, _, hz⟩ := hinner P (MulAut.conjNormal v) (by
    intro x hx
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hxS : (x : G) ∈ S := by
      change x ∈ (P : Subgroup L) at hx
      rwa [hP] at hx
    rw [← hc x hxS, mul_inv_cancel_right])
  have hv : v = (z : G) :=
    MulAut.conjNormal_injective_of_centralizer_eq_bot L hfaith
      (hz.trans MulAut.conjNormal_val.symm)
  exact hv ▸ z.property

/-- The original Sylow subgroup restricts to an intrinsic Sylow subgroup
centralized by the same element of L. -/
theorem exists_sylow_centralized_of_ambient
    (L : Subgroup G) [L.Normal] (S : Sylow 2 G) (v : L)
    (hc : ∀ x ∈ S, x * (v : G) = (v : G) * x) :
    ∃ P : Sylow 2 L, (P : Subgroup L) = (S : Subgroup G).subgroupOf L ∧
      ∀ x ∈ P, x * v = v * x := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal L
  refine ⟨P, hP, ?_⟩
  intro x hx
  apply Subtype.ext
  apply hc
  change x ∈ (P : Subgroup L) at hx
  rwa [hP] at hx

end Theory.GroupTheory
