module
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transporting relative normalizer invariance

Conjugation by an element of A ∩ N(L) preserves A ∩ L. After marking that
intersection as R in another group, it induces an automorphism preserving R.
A subgroup invariant under all such automorphisms therefore pulls back to a
subgroup normalized by A ∩ N(L). The ambient subgroup A may permute conjugates
of L; only its relative normalizer acts on L itself.

This is the elementary transport used for invariant parabolics in
Aschbacher–Smith 2.3.9(7), printed p.526.
-/

namespace Subgroup
open Subgroup
variable {G : Type*} [Group G] {L A : Subgroup G}

private theorem normalizerAction_preserves_intersection
    (s : normalizer (L : Set G)) (hs : (s : G) ∈ A) :
    (A.subgroupOf L).map (L.normalizerMonoidHom s).toMonoidHom = A.subgroupOf L := by
  have hf (u : normalizer (L : Set G)) (hu : (u : G) ∈ A) {x : L}
      (hx : x ∈ A.subgroupOf L) : L.normalizerMonoidHom u x ∈ A.subgroupOf L := by
    change (L.normalizerMonoidHom u x : G) ∈ A
    rw [normalizerMonoidHom_apply_apply_coe]
    exact A.mul_mem (A.mul_mem hu hx) (A.inv_mem hu)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hf s hs hy
  · intro hx
    refine ⟨L.normalizerMonoidHom s⁻¹ x, hf s⁻¹ (A.inv_mem hs) hx, ?_⟩
    have he := map_inv L.normalizerMonoidHom s
    rw [he]
    exact (L.normalizerMonoidHom s).apply_symm_apply x

end Subgroup

namespace Subgroup
open Subgroup
variable {G K : Type*} [Group G] [Group K] {L A : Subgroup G}

/-- Transport stabilizer invariance to the relative normalizer A ∩ N(L).
No normality of L in A is assumed. -/
public theorem normalizes_pullback_of_stabilizer_invariant
    (e : L ≃* K) (R P : Subgroup K)
    (hR : (A.subgroupOf L).map e.toMonoidHom = R)
    (hP : ∀ β : MulAut K, R.map β.toMonoidHom = R → P.map β.toMonoidHom = P) :
    A ⊓ normalizer (L : Set G) ≤
      normalizer ((P.map e.symm.toMonoidHom).map L.subtype : Set G) := by
  intro s hs
  let n : normalizer (L : Set G) := ⟨s, hs.2⟩
  let α := L.normalizerMonoidHom n
  let β : MulAut K := e.symm.trans (α.trans e)
  have hαR : (A.subgroupOf L).map α.toMonoidHom = A.subgroupOf L :=
    normalizerAction_preserves_intersection n hs.1
  have hβR : R.map β.toMonoidHom = R := by
    rw [← hR, Subgroup.map_map]
    have he : β.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp α.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, β, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [he, ← Subgroup.map_map, hαR]
  have hαP : (P.map e.symm.toMonoidHom).map α.toMonoidHom = P.map e.symm.toMonoidHom := by
    rw [Subgroup.map_map]
    have he : α.toMonoidHom.comp e.symm.toMonoidHom =
        e.symm.toMonoidHom.comp β.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, β, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [he, ← Subgroup.map_map, hP β hβR]
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he : ((MulAut.conj s : MulAut G) : G →* G).comp L.subtype = L.subtype.comp α.toMonoidHom := by
    ext x
    exact (normalizerMonoidHom_apply_apply_coe L n x).symm
  rw [Subgroup.map_map, he, ← Subgroup.map_map, hαP]

end Subgroup
