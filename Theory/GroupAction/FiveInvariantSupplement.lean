module

public import Theory.GroupAction.FiveInvariantIndexTwo
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Uniqueness of an invariant index-two supplement

Suppose an action on P/F has image divisible by five and |P/F| = 16.
Two invariant index-two subgroups with the same intersection with F,
one supplementing F, coincide. Their intersection cannot have trivial
image in P/F: its index is at most four. Irreducibility therefore makes
its image full, and the index formula identifies the two subgroups.

The quotient-invariance lemma connects this argument to actual conjugation
on a normal subgroup. The application is the additional omega subgroup
in the corrected full-Ree argument of Aschbacher--Smith, Lemma 14.2.21,
printed p.989. No containment of F in the candidate is assumed.
-/

namespace Theory.GroupAction

open Subgroup

public theorem invariant_index_two_supplement_unique {A P : Type*} [Group A] [Group P] [Finite P]
    (F Q W : Subgroup P) [F.Normal] [Q.Normal] [W.Normal]
    (ρ : A →* MulAut (P ⧸ F))
    (hI : ∀ a : A, ∀ v : P ⧸ F,
      v ∈ (Q ⊓ W).map (QuotientGroup.mk' F) ↔
        ρ a v ∈ (Q ⊓ W).map (QuotientGroup.mk' F))
    (hinter : Q ⊓ F = W ⊓ F) (hW : W ⊔ F = ⊤)
    (hQindex : Q.index = 2) (hWindex : W.index = 2)
    (hA : 5 ∣ Nat.card ρ.range) (hV : Nat.card (P ⧸ F) = 16) : Q = W := by
  have same_index (B C : Subgroup P) (hBC : B ≤ C) (hi : B.index = C.index) : B = C := by
    by_contra hne
    have := index_strictAnti (lt_of_le_of_ne hBC hne)
    omega
  rcases Theory.GroupAction.invariant_eq_bot_or_top_of_image_five ρ hA hV
      ((Q ⊓ W).map (QuotientGroup.mk' F)) hI with hb | ht
  · have hle : Q ⊓ W ≤ F := by simpa using (map_eq_bot_iff (Q ⊓ W)).mp hb
    have hlow := index_antitone hle
    have hupp := index_inf_le (H := Q) (K := W)
    rw [hQindex, hWindex] at hupp
    change F.index = 16 at hV
    omega
  · have hjoin : (Q ⊓ W) ⊔ F = ⊤ := by
      have hm : ((Q ⊓ W) ⊔ F).map (QuotientGroup.mk' F) = ⊤ := by
        rw [Subgroup.map_sup, ht, top_sup_eq]
      have hc := congrArg (Subgroup.comap (QuotientGroup.mk' F)) hm
      rwa [Subgroup.comap_map_eq_self (by simp), Subgroup.comap_top] at hc
    have hi : (Q ⊓ W) ⊓ F = W ⊓ F := by
      rw [inf_assoc, inf_left_comm, hinter, inf_left_idem]
    have hix := relIndex_sup_left F (Q ⊓ W)
    have hwx := relIndex_sup_left F W
    rw [hjoin, relIndex_top_right, ← inf_relIndex_right, hi] at hix
    rw [hW, relIndex_top_right, ← inf_relIndex_right] at hwx
    have he : Q ⊓ W = Q := same_index _ _ inf_le_left (by omega)
    exact same_index Q W (he ▸ inf_le_right) (by omega)

public theorem normal_subgroup_quotient_invariant {H : Type*} [Group H]
    (P Q : Subgroup H) [P.Normal] [Q.Normal]
    (F : Subgroup P) [F.Characteristic] :
    ∀ g : H, ∀ v : P ⧸ F,
      v ∈ (Q.subgroupOf P).map (QuotientGroup.mk' F) ↔
        quotientAut F (MulAut.conjNormal g) v ∈
          (Q.subgroupOf P).map (QuotientGroup.mk' F) := by
  have forward (g : H) (v : P ⧸ F)
      (hv : v ∈ (Q.subgroupOf P).map (QuotientGroup.mk' F)) :
      quotientAut F (MulAut.conjNormal g) v ∈
        (Q.subgroupOf P).map (QuotientGroup.mk' F) := by
    obtain ⟨x,hx,rfl⟩ := hv
    rw [quotientAut_apply_mk]
    exact mem_map_of_mem _ ((inferInstance : Q.Normal).conj_mem x hx g)
  intro g v
  refine ⟨forward g v, fun hv => ?_⟩
  have h := forward g⁻¹ _ hv
  simpa only [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply] using h


end Theory.GroupAction
