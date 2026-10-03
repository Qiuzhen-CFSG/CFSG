module
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow conjugacy inside a normalized subgroup

Let S be a Sylow p-subgroup of a finite group and C a subgroup normalized by
S. Every p-subgroup W contained in C can be conjugated into S using an
element of C. This is a standard form of the Sylow intersection theorem.

Apply Sylow conjugacy in the product SC and factor the resulting conjugator
as sc. The first factor normalizes S, so the C factor already conjugates W
into S. The application in Stellmacher (9.8) takes C to be a relative center
centralizer and uses the conjugator to choose a terminal neighbor core.
-/

open scoped Pointwise

public theorem IsPGroup.exists_conj_le_sylow_of_normalized
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (C W : Subgroup G)
    (hC : (S : Subgroup G) ≤ Subgroup.normalizer (C : Set G))
    (hW : IsPGroup p W) (hWC : W ≤ C) :
    ∃ c : G, c ∈ C ∧ W.map (MulAut.conj c).toMonoidHom ≤ (S : Subgroup G) := by
  classical
  let D : Subgroup G := (S : Subgroup G) ⊔ C
  let restricted : Sylow p D := S.subtype le_sup_left
  have hWD : W ≤ D := hWC.trans le_sup_right
  obtain ⟨other, hother⟩ := (hW.comap_of_injective D.subtype D.subtype_injective).exists_le_sylow
  obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq D other restricted
  have hfactor : (actor : G) ∈ (S : Subgroup G) ⊔ C := actor.property
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hC] at hfactor
  obtain ⟨s, hs, c, hc, hsc⟩ := hfactor
  refine ⟨c, hc, ?_⟩
  rintro element ⟨w, hw, rfl⟩
  have hwOther : (⟨w, hWD hw⟩ : D) ∈ (other : Subgroup D) := hother hw
  have hconj : actor * (⟨w, hWD hw⟩ : D) * actor⁻¹ ∈ (restricted : Subgroup D) := by
    rw [← hactor]
    exact Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom hwOther
  change (actor : G) * w * (actor : G)⁻¹ ∈ (S : Subgroup G) at hconj
  apply (Subgroup.mem_normalizer_iff.mp ((S : Subgroup G).le_normalizer hs) _).mpr
  change s * (c * w * c⁻¹) * s⁻¹ ∈ (S : Subgroup G)
  simpa only [← hsc, mul_inv_rev, mul_assoc] using hconj
