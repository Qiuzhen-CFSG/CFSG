module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SmallActionUniqueness
public import Theory.GroupTheory.SylowPrimeIndex
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# Maximal overgroups for prime-index Sylow action images

A third maximal two-local overgroup has an intersection with M escaping
Mc. Its action image contains the original Sylow image. It cannot be a
two-group, since it would then lift into the Sylow times the action kernel,
both contained in Mc. Prime Sylow index forces the whole action image,
contradicting the proved central-seed span uniqueness.

The concrete D10 and Sz(2) actions have orders ten and twenty, respectively,
so their Sylow index is five. This proves their original15.2.5 rows. The
case with an additional cubic Fitting factor remains separate.

Source: Aschbacher--Smith15.2.5, printed p.1107.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
theorem PreparedChosenModule.maximal_overgroups_of_prime_action_sylow_index
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hp : ∀ P : Sylow 2 (internalActionImage M V hV.normalized),
      Nat.Prime (P : Subgroup (internalActionImage M V hV.normalized)).index) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc} := by
  classical
  let := hV.elementary
  let D := internalActionImage M V hV.normalized
  let f : M →* D := (actionHom M V hV.normalized).rangeRestrict
  have hf : Function.Surjective f := (actionHom M V hV.normalized).rangeRestrict_surjective
  let P := (T.subtype hM.1.2).mapSurjective hf
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  ext N
  constructor
  · intro hN
    by_cases hNM : N = M
    · simp [hNM]
    have ho := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
    let H := M ⊓ N
    have hTH : (T : Subgroup G) ≤ H := le_inf hM.1.2 hN.2
    have hHout (hNMc : N ≠ Mc) : ¬ H ≤ Mc := by
      intro hH
      have hle : N ≤ Mc := by
        intro x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := ho x hx
        exact Mc.mul_mem (hH ⟨ha.2,ha.1⟩)
          (localModule_centralizer_le_partner T N hu hb.2)
      exact hNMc (le_antisymm hle (hN.1.2 hMc.1.1 hle))
    by_cases hNMc : N = Mc
    · simp [hNMc]
    let A := (H.subgroupOf M).map f
    have hPA : (P : Subgroup D) ≤ A := map_mono (show (T : Subgroup G).subgroupOf M ≤
        H.subgroupOf M from comap_mono hTH)
    have hAnot : ¬ IsPGroup 2 A := by
      intro hA
      have hAP : A ≤ (P : Subgroup D) := (P.is_maximal' hA hPA).le
      apply hHout hNMc
      intro x hx
      have hxA : f ⟨x,hx.1⟩ ∈ A := mem_map_of_mem f hx
      obtain ⟨t, ht, he⟩ := hAP hxA
      have hk : t⁻¹ * (⟨x,hx.1⟩ : M) ∈ f.ker := by
        change f (t⁻¹ * ⟨x,hx.1⟩) = 1
        rw [map_mul,map_inv,he,inv_mul_cancel]
      have hk' : t⁻¹ * (⟨x,hx.1⟩ : M) ∈ (actionHom M V hV.normalized).ker := by
        exact congrArg (fun d : D => (d : MulAut V)) hk
      rw [actionHom_ker] at hk'
      have hxc : (t : G)⁻¹ * x ∈ Mc := hV.centralizer_le_partner T hu hk'
      have hh : (t : G) * ((t : G)⁻¹ * x) ∈ Mc := Mc.mul_mem (hTMc ht) hxc
      simpa only [mul_inv_cancel_left] using hh
    have hAtop : A = ⊤ := Subgroup.eq_top_of_sylow_le_of_prime_index P A hPA hAnot (hp P)
    have himage : (actionHom M V hV.normalized).range ≤
        (H.subgroupOf M).map (actionHom M V hV.normalized) := by
      rintro x ⟨m,rfl⟩
      have hm : f m ∈ A := hAtop ▸ mem_top _
      obtain ⟨y,hy,he⟩ := hm
      exact ⟨y,hy,congrArg (fun d : D => (d : MulAut V)) he⟩
    have huniq := Section02.source_unique_overgroup_of_full_action hG T hempty hM hJ
      hV hTH inf_le_left himage
    exact (hNM (Set.mem_singleton_iff.mp (huniq ▸
      (show N ∈ maximalTwoLocalOvergroups H from ⟨hN.1,inf_le_right⟩)))).elim
  · intro hN
    rcases Set.mem_insert_iff.mp hN with rfl | hN
    · exact hM.1
    · obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hMc.1,hTMc⟩


theorem PreparedChosenModule.maximal_overgroups_of_action_card_ten_or_twenty
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hc : Nat.card (internalActionImage M V hV.normalized) = 10 ∨
      Nat.card (internalActionImage M V hV.normalized) = 20) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc} := by
  apply hV.maximal_overgroups_of_prime_action_sylow_index hG T hempty hM hJ hu
  intro P
  rw [sylow_index_five_of_card_ten_or_twenty P hc]
  decide

theorem PreparedChosenModule.maximal_overgroups_of_five_action_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (he : Nonempty (internalActionImage M V hV.normalized ≃* DihedralGroup 5) ∨
      Nonempty (internalActionImage M V hV.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc} := by
  apply hV.maximal_overgroups_of_action_card_ten_or_twenty hG T hempty hM hJ hu
  rcases he with he | he
  · obtain ⟨e⟩ := he
    exact Or.inl ((Nat.card_congr e.toEquiv).trans (by
      rw [Nat.card_eq_fintype_card]
      decide))
  · obtain ⟨e⟩ := he
    exact Or.inr ((Nat.card_congr e.toEquiv).trans
      BenderSuzuki.MatrixGroups.suzukiZero_card)
end CFSG.Quasithin.Chapter15.Section01
