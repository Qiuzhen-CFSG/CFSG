module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticMiddleCorePointMovement
public import Theory.SpecificGroups.ReeTwo.InvertingExtensionFirstCore

/-!
# The characteristic first core in the original Sylow subgroup

The original plane lies in the second center of the Sylow subgroup. Hence
its characteristic first core lies in the actual middle two-core. Their
orders force equality whenever the first core has order 2048, so the
original point mover excludes a fixed marked point in that case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem normal_four_le_second_center
    {K : Type*} [Group K] [Finite K] (V Z : Subgroup K) [V.Normal]
    (hV : Nat.card V = 4) (hZ : Nat.card Z = 2)
    (hZV : Z ≤ V) (hZc : Z ≤ center K) :
    V ≤ Subgroup.upperCentralSeries K 2 := by
  let q := QuotientGroup.mk' (center K)
  have hc := relIndex_mul_card_of_le (show V ⊓ center K ≤ V from inf_le_left)
  rw [inf_relIndex_left, ← QuotientGroup.ker_mk' (center K), relIndex_ker,
    QuotientGroup.ker_mk'] at hc
  have hl := card_le_of_le (le_inf hZV hZc)
  rw [hZ] at hl
  rw [hV] at hc
  have hp := Nat.card_pos (α := V.map q)
  have hle : Nat.card (V.map q) ≤ 2 := by
    change Nat.card (V.map q) * Nat.card (V ⊓ center K : Subgroup K) = 4 at hc
    nlinarith
  have hcent : V.map q ≤ center (K ⧸ center K) := by
    have : (V.map q).Normal :=
      Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    rcases (by omega : Nat.card (V.map q) = 1 ∨ Nat.card (V.map q) = 2) with hh | hh
    · rw [card_eq_one.mp hh]; exact bot_le
    · exact central_of_normal_card_two _ hh
  rw [← Subgroup.comap_upperCentralSeries_quotient_center 1, Subgroup.upperCentralSeries_one]
  exact map_le_iff_le_comap.mp hcent

/-- The original plane controls the intrinsic first core; the large branch
also determines the orders of both original endpoints and the middle core. -/
theorem source_quintic_large_sylow_first_core_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024) :
    let QX := (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2
    Nat.card H = 20480 ∧ Nat.card (T : Subgroup G) = 4096 ∧ Nat.card QX = 2048 ∧
      (localModule T M).subgroupOf (T : Subgroup G) ≤ Subgroup.upperCentralSeries T 2 ∧
      (ReeTwo.InvertingExtension.firstCore T).map (T : Subgroup G).subtype ≤ QX := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let V := localModule T M
  let Z := centralInvolutions T
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy V H
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hH.1.1.2)).trans_eq
      (map_subgroupOf_eq_of_le hH.1.1.2)
  have hUQ : U ≤ Q := (source_quintic_full_core_layers
    hG T hempty hM hu hmany hcard e H hH hi).1.ge.trans (commutator_le_self _)
  have hVT : V ≤ (T : Subgroup G) := (le_conjugateSpanBy _ _).trans (hUQ.trans hQT)
  have hZT : Z ≤ (T : Subgroup G) := centralInvolutions_le_sylow T
  have hnV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    hM.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  let : (V.subgroupOf (T : Subgroup G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVT).mpr hnV
  have hZV : Z.subgroupOf (T : Subgroup G) ≤ V.subgroupOf (T : Subgroup G) :=
    fun _ hz => le_conjugateSpanBy _ _ hz
  have hZc : Z.subgroupOf (T : Subgroup G) ≤ center T := by
    intro z hz
    apply mem_center_iff.mpr
    intro t
    exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz t t.property)
  have hV2 : V.subgroupOf (T : Subgroup G) ≤ Subgroup.upperCentralSeries T 2 :=
    normal_four_le_second_center _ _
      ((Nat.card_congr (subgroupOfEquivOfLe hVT).toEquiv).trans hcard)
      ((Nat.card_congr (subgroupOfEquivOfLe hZT).toEquiv).trans
        (plane_centralInvolutions_card T M hM.1.2 hcard e)) hZV hZc
  obtain ⟨hQX,⟨eX⟩⟩ := Section02.source_residualSylow_quotient
    hG T hempty hM hu hmany hcard e
  have hKQX : (ReeTwo.InvertingExtension.firstCore T).map
      (T : Subgroup G).subtype ≤ X.pCoreIn 2 := by
    rw [hQX]
    rintro x ⟨t,ht,rfl⟩
    refine ⟨hTX t.property,?_⟩
    intro v hv
    have he := ht ⟨v,hVT hv⟩ (hV2 hv)
    exact congrArg (fun x : T => (x : G)) he
  obtain ⟨_,⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient
    hG T hempty hM hu hmany hcard e H hH hi
  have hquot : Nat.card (H ⧸ pCore 2 H) = 20 :=
    (Nat.card_congr eSuz.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
  have hcore : Nat.card (pCore 2 H) = 1024 :=
    (card_map_of_injective H.subtype_injective).symm.trans hlarge
  have hHcard : Nat.card H = 20480 := by
    have hh := (pCore 2 H).card_mul_index
    rw [index_eq_card,hcore,hquot] at hh
    exact hh.symm
  have hTcard : Nat.card (T : Subgroup G) = 4096 := by
    have hh := relIndex_mul_card_of_le hH.1.1.2
    rw [hi,hHcard] at hh
    omega
  have hiX : (T : Subgroup G).relIndex X = 3 :=
    SymmetricThreeTwoCore.sylow_index_three eX (T.subtype hTX)
  have hXcard : Nat.card X = 12288 := by
    have hh := relIndex_mul_card_of_le hTX
    rw [hiX,hTcard] at hh
    exact hh.symm
  have hquotX : Nat.card (X ⧸ pCore 2 X) = 6 := by
    rw [Nat.card_congr eX.toEquiv]
    rw [Nat.card_perm,Nat.card_fin]
    rfl
  have hQXcard : Nat.card (X.pCoreIn 2) = 2048 := by
    change Nat.card ((pCore 2 X).map X.subtype) = 2048
    rw [card_map_of_injective X.subtype_injective]
    have hh := (pCore 2 X).card_mul_index
    rw [index_eq_card,hquotX,hXcard] at hh
    omega
  exact ⟨hHcard,hTcard,hQXcard,hV2,hKQX⟩

/-- The order-2048 first core cannot fix the original marked central point
under every automorphism: it would equal the actual middle core. -/
theorem source_quintic_large_first_core_mark_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (z : T) (hz : (z : G) ∈ centralInvolutions T) (hz1 : z ≠ 1) :
    ¬ (Nat.card (ReeTwo.InvertingExtension.firstCore T) = 2048 ∧
      ∃ hk : z ∈ ReeTwo.InvertingExtension.firstCore T,
        ∀ α : MulAut (ReeTwo.InvertingExtension.firstCore T),
          α ⟨z,hk⟩ = ⟨z,hk⟩) := by
  rintro ⟨hKcard,hk,hfixed⟩
  let K := ReeTwo.InvertingExtension.firstCore T
  let QX := (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨_,_,hQXcard,_,hKQX⟩ := source_quintic_large_sylow_first_core_geometry
    hG T hempty hM hu hmany hcard e H hH hi hlarge
  have hKeq : K.map (T : Subgroup G).subtype = QX := eq_of_le_of_card_ge hKQX (by
    rw [card_map_of_injective (T : Subgroup G).subtype_injective,hKcard,hQXcard])
  let d : K ≃* QX := (equivMapOfInjective K (T : Subgroup G).subtype
    (T : Subgroup G).subtype_injective).trans (MulEquiv.subgroupCongr hKeq)
  obtain ⟨hzQX,α,hα⟩ := source_quintic_middle_core_point_moved
    hG T hempty hM hu hmany hcard e H hH hi z hz (fun hh => hz1 (Subtype.ext hh))
  let β : MulAut K := d.trans (α.trans d.symm)
  have hb := congrArg d (hfixed β)
  have he : d ⟨z,hk⟩ = (⟨(z:G),hzQX⟩ : QX) := Subtype.ext rfl
  have hb' : α (d ⟨z,hk⟩) = d ⟨z,hk⟩ := by
    simpa only [β, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using hb
  rw [he] at hb'
  exact hα (congrArg (fun x : QX => (x:G)) hb')

end CFSG.Quasithin.Chapter14.Section06
