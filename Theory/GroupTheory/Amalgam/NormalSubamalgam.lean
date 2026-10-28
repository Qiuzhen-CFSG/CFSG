module

public import Theory.GroupTheory.Amalgam.SylowRigidity
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Faithfulness inherited by a normal subamalgam

Let a normal subgroup H be supplemented by an overlap T. A subgroup K of T
normalized by H has its entire normal closure inside T: factor an ambient
conjugator as t*h and first use H-normalization of K. Consequently, absence
of an ambient normal subgroup inside T passes to the restricted normal group.
This is the faithfulness step for Goldschmidt's two-perfect subamalgam.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (3.2),
printed pp.386--387. No finiteness or group classification is required.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Conjugating a normalizer-invariant subgroup through a normal supplement
keeps its normal closure inside the original overlap. -/
theorem normalClosure_le_of_normal_supplement (H T K : Subgroup G) [H.Normal]
    (hgen : H ⊔ T = ⊤) (hHK : H ≤ normalizer (K : Set G)) (hKT : K ≤ T) :
    normalClosure (K : Set G) ≤ T := by
  apply (Subgroup.closure_le (K := T)).mpr
  intro x hx
  obtain ⟨k, hk, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  have hg : g ∈ T ⊔ H := by rw [sup_comm, hgen]; trivial
  obtain ⟨t, ht, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hhkh : h * k * h⁻¹ ∈ K := (mem_normalizer_iff.mp (hHK hh) k).mp hk
  change (t * h) * k * (t * h)⁻¹ ∈ T
  simpa only [mul_inv_rev, mul_assoc] using T.mul_mem (T.mul_mem ht (hKT hhkh)) (T.inv_mem ht)

/-- A normal subgroup whose supplement contains no ambient normal subgroup
inherits that same faithful-overlap property. -/
theorem normal_subgroup_overlap_eq_bot (H T : Subgroup G) [H.Normal]
    (hgen : H ⊔ T = ⊤)
    (hfaith : ∀ K : Subgroup G, K.Normal → K ≤ T → K = ⊥)
    (K : Subgroup H) [K.Normal] (hKT : K ≤ T.subgroupOf H) : K = ⊥ := by
  let L := K.map H.subtype
  have hHL := K.le_normalizer_map H.subtype
  simp only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hHL
  have hLT : L ≤ T := map_le_iff_le_comap.mpr hKT
  have he := hfaith (normalClosure (L : Set G)) inferInstance
    (normalClosure_le_of_normal_supplement H T L hgen hHL hLT)
  have hL : L = ⊥ := le_bot_iff.mp (le_normalClosure.trans he.le)
  exact (map_eq_bot_iff_of_injective K H.subtype_injective).mp hL

end Subgroup
