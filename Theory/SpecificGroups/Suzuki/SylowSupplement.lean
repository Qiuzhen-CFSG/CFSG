module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupAction.SylowPointwiseInner

/-!
# Sylow supplements of a two-core extension of a Suzuki group

Let T be an ambient Sylow two-subgroup normalizing A, with A/O₂(A) a
nondegenerate Suzuki group. The actual action of AT on A/O₂(A) has kernel
O₂(AT), and every image of a T-element is inner because the Suzuki outer
automorphism group has odd order. Lifting its inner implementer gives
T = O₂(AT)(T ∩ A), with all factors in the original ambient group.

This supplies the Sylow factorization used in Aschbacher–Smith F.1.10(1)
and the normality premise of F.1.12, printed pp.262–264. Its application to
the original A₅–Suzuki pair is in SuzukiIsolation.SourceSylow.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups

private theorem suzuki_center (m : ℕ) (hm : 0 < m) :
    center (SuzukiMatrixGroup m) = ⊥ := by
  let := (External.huppert_blackburn_XI_3_6 m hm).1
  rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (External.suzukiMatrixGroup_not_isSolvable m hm
      (Group.isSolvable_of_comm (fun x y => by
        have hx : x ∈ center (SuzukiMatrixGroup m) := h ▸ mem_top x
        exact (mem_center_iff.mp hx y).symm))).elim

/-- An ambient Sylow is the product of the extended two-core and its
intersection with a normalized subgroup having Suzuki two-core quotient. -/
theorem suzuki_quotient_sylow_factorization {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (T : Sylow 2 G)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    {m : ℕ} (hm : 0 < m) (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m) :
    (T : Subgroup G) = (A ⊔ (T : Subgroup G)).pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ A) := by
  let H := A ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let f := pCoreJoinAction 2 hTA
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    apply bot_unique
    intro x hx
    apply e.injective
    have he : e x ∈ center (SuzukiMatrixGroup m) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨a, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx a)
    simpa only [suzuki_center m hm, mem_bot, map_one] using he
  have hk : f.ker = pCore 2 H := pCoreJoinAction_kernel 2 hTA T.isPGroup' hz
  have hodd : Odd (MulAut.conj : (A ⧸ pCore 2 A) →* MulAut (A ⧸ pCore 2 A)).range.index := by
    change Odd (Nat.card (MulAut.Outer (A ⧸ pCore 2 A)))
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact suzuki_odd_outer_index m (by omega)
  have himage : (S : Subgroup H).map f ≤ MulAut.innerSubgroup (A ⧸ pCore 2 A) := by
    rintro α ⟨s, hs, rfl⟩
    obtain ⟨k, hkpow⟩ := S.isPGroup' ⟨s, hs⟩
    have hp : f s ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      exact (congrArg f (congrArg Subtype.val hkpow)).trans f.map_one
    obtain ⟨x, hx⟩ := MulAut.inner_of_two_pow_eq_one_of_odd_index hodd (f s) hp
    exact ⟨x, hx.symm⟩
  have hAimage : (A.subgroupOf H).map f = MulAut.innerSubgroup (A ⧸ pCore 2 A) := by
    apply le_antisymm
    · rintro α ⟨a, ha, rfl⟩
      let a₀ : A := ⟨a.val, ha⟩
      have he : inclusion (show A ≤ H from le_sup_left) a₀ = a := Subtype.ext rfl
      rw [← he, pCoreJoinAction_on_component]
      exact ⟨_, rfl⟩
    · rintro α ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) x
      exact ⟨inclusion le_sup_left a, a.property, pCoreJoinAction_on_component 2 hTA a⟩
  have hfact := f.sylow_eq_pCore_sup_inf_of_image_le S (A.subgroupOf H)
    (hk.symm ▸ (pCore_isPGroup (p := 2) (G := H)))
    (pCore_range_eq_bot_of_ker_eq_pCore 2 f hk) (himage.trans hAimage.ge)
  have hmap := congrArg (Subgroup.map H.subtype) hfact
  have hS : (S : Subgroup H).map H.subtype = (T : Subgroup G) := by
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le]
    exact le_sup_right
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le (show A ≤ H from le_sup_left), hS] at hmap
  exact hmap

end BenderSuzuki.MatrixGroups
