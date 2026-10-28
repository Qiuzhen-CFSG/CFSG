module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalBlockMaximal
public import Theory.GroupTheory.Recognition.QuasithinM23.ExceptionalLocal
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original exceptional local and core orders in source 5.2.11

In the nonmaximal linear row, the existing overcomponent theorem supplies
an exceptional A₇ subgroup J with the same two-core as K = O²(H). The
Sylow-containing group JT has that very core: subnormality gives one
inclusion and the original H gives the other. Its faithful action on the
elementary sixteen-group forces JT = J. The same argument in N_G(J),
together with source 1.2.7, makes J maximal two-local and identifies both
N_G(O₂(J)) and C_G(O₂(J)).

The compatible linear comparison also identifies both original factor cores
as elementary groups of order sixteen. It identifies O₂(N_G(L)) with O₂(L)
and gives its full ambient normalizer and centralizer. Finally the actual
Sylow orders are |T| = 128 and |S| = 64, proving |T:S| = 2. S remains the
two-core of the original intersection, not the whole Borel.

These prove the maximal-local and Sylow-index clauses 5.2.11(4),(5) and
the preceding core identifications. The pair/triple markings, ΓL₂(4)
quotient, fusion, and ambient M₂₃ recognition are separate steps.
Source: Aschbacher–Smith 5.2.11, printed pp.653–654 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem exceptional_overgroup_eq
    {J X : Subgroup G} (hJX : J ≤ X) (hsub : (J.subgroupOf X).IsSubnormal)
    (hchar : HasCharacteristicTwo X)
    (hc : X.pCoreIn 2 = J.pCoreIn 2)
    (ha : IsElementaryAbelian 2 (pCore 2 J))
    (hcard : Nat.card (pCore 2 J) = 16)
    (e : J ⧸ pCore 2 J ≃* alternatingGroup (Fin 7)) : X = J := by
  let a : pCore 2 X ≃* pCore 2 J :=
    ((pCore 2 X).equivMapOfInjective X.subtype X.subtype_injective).trans
      ((MulEquiv.subgroupCongr hc).trans
        ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).symm)
  let : IsElementaryAbelian 2 (pCore 2 X) :=
    IsElementaryAbelian.of_injective a.toMonoidHom a.injective
  have hcardX : Nat.card (pCore 2 X) = 16 := (Nat.card_congr a.toEquiv).trans hcard
  have hcore : (J.subgroupOf X).pCoreIn 2 = pCore 2 X := by
    rw [pCoreIn_subgroupOf 2 J X hJX, ← hc]
    exact comap_map_eq_self_of_injective X.subtype_injective _
  let eJ := subgroupOfEquivOfLe hJX
  let eQ := (QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)).trans e
  have ht := QuasithinM23.eq_top_of_subnormal_alternatingSeven
    (pCore 2 X) hcardX hchar (J.subgroupOf X) hsub hcore eQ
  exact le_antisymm (subgroupOf_eq_top.mp ht) hJX

/-- The actual exceptional overcomponent contains T and is itself maximal
two-local; its normalizers and full core centralizer are literal ambient ones. -/
theorem Preparation.linear_exceptional_local
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : residual H < J) :
    (T : Subgroup G) ≤ J ∧ H ≤ J ∧ IsMaximalTwoLocal J ∧
      normalizer (J : Set G) = J ∧
      normalizer (J.pCoreIn 2 : Set G) = J ∧
      centralizer (J.pCoreIn 2 : Set G) = J.pCoreIn 2 ∧
      H.pCoreIn 2 = J.pCoreIn 2 ∧
      Nat.card J = 40320 := by
  have hTH := hH.1.1.2
  have hn := (d.block_overcomponent_parameter h hTH hp F hm hF (.inl he) hJ.1 hKJ).1
  have hblock := d.linear_four_overcomponent_exceptional (hn ▸ h) hTH hp F hm hF he hJ.1 hKJ
  obtain ⟨ha,hcard,_⟩ := d.linear_overcomponent_action h hTH hp F hm hF he hJ.1 hKJ.le
  rw [hn] at hcard
  have hcard : Nat.card (pCore 2 J) = 16 := hcard
  have hJK := (d.linear_overcomponent_core h hTH hp F hm hF he hJ.1 hKJ.le).1
  have hHK : H.pCoreIn 2 = (residual H).pCoreIn 2 :=
    residual_core_eq_of_sourceS_le h.sylow_normalizes hTH
      (d.linear_sourceS_le_factors h hTH hp F hm hF he 1)
  have hHJ : H ≤ J ⊔ (T : Subgroup G) := by
    rw [← residual_sup_sylow T H hTH]
    exact sup_le_sup hKJ.le le_rfl
  have hcore : (J ⊔ (T : Subgroup G)).pCoreIn 2 = J.pCoreIn 2 := by
    apply le_antisymm
    · exact (Chapter3.twoCore_le_of_sylow_le T hTH hHJ).trans_eq (hHK.trans hJK.symm)
    · exact pCoreAmbient_mono_of_isSubnormalIn J _ 2 le_sup_left hJ.1.1.subnormal
  have hchar := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T)
      ⟨hJ.1.2.2, show (T : Subgroup G) ≤ J ⊔ (T : Subgroup G) from le_sup_right⟩)
  have heq : J ⊔ (T : Subgroup G) = J :=
    exceptional_overgroup_eq le_sup_left hJ.1.1.subnormal hchar hcore ha hcard hblock.2.1.some
  have hTJ : (T : Subgroup G) ≤ J := heq ▸ le_sup_right
  have hOrbit : componentOrbit J (T : Subgroup G) = J :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (hTJ.trans J.le_normalizer)) (le_componentOrbit _ _)
  have hmax := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hJ).normalizer_maximal
  rw [hOrbit] at hmax
  have hTN := hTJ.trans J.le_normalizer
  have hcharN := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T)
      ⟨Chapter1.mem_H_of_isTwoLocal hmax.1, hTN⟩)
  have hcoreN : (normalizer (J : Set G)).pCoreIn 2 = J.pCoreIn 2 :=
    le_antisymm (Chapter3.twoCore_le_of_sylow_le T hTJ J.le_normalizer)
      (pCoreIn_mono_of_normalizes J.le_normalizer le_rfl)
  have hNJ : normalizer (J : Set G) = J :=
    exceptional_overgroup_eq J.le_normalizer
      (normal_subgroupOf_of_le_normalizer le_rfl).isSubnormal
      hcharN hcoreN ha hcard hblock.2.1.some
  have hmaxJ : IsMaximalTwoLocal J := hNJ ▸ hmax
  have hUne : J.pCoreIn 2 ≠ ⊥ := by
    intro hz
    have hh := card_map_of_injective (K := pCore 2 J) J.subtype_injective
    change Nat.card (J.pCoreIn 2) = Nat.card (pCore 2 J) at hh
    rw [hz, card_bot, hcard] at hh
    omega
  have hJU : J ≤ normalizer (J.pCoreIn 2 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hNU : normalizer (J.pCoreIn 2 : Set G) = J :=
    le_antisymm (hmaxJ.2 ⟨_,hUne,isPGroup_pCoreIn 2 J,rfl⟩ hJU) hJU
  have hCU : centralizer (J.pCoreIn 2 : Set G) = J.pCoreIn 2 := by
    apply le_antisymm
    · exact fun x hx => (Chapter1.mem_He_iff.mpr
        (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
          (h.qtke.evenCharacteristic T) hJ.1))
        ⟨hNU ▸ Subgroup.centralizer_le_normalizer _ hx,hx⟩
    · let := ha
      let : IsMulCommutative (J.pCoreIn 2) :=
        inferInstanceAs (IsMulCommutative ((pCore 2 J).map J.subtype))
      exact fun x hx => mem_centralizer_iff.mpr (fun y hy => setLike_mul_comm hy hx)
  refine ⟨hTJ,heq ▸ hHJ,hmaxJ,hNJ,hNU,hCU,hHK.trans hJK.symm,?_⟩
  have hqcard : Nat.card (J ⧸ pCore 2 J) = 2520 := by
    rw [Nat.card_congr hblock.2.1.some.toEquiv,nat_card_alternatingGroup]
    norm_num
  rw [← (pCore 2 J).card_mul_index, index_eq_card, hcard, hqcard]


private theorem linear_factor_affine
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (i : Fin 2) : Nonempty (![L,residual H] i ≃* Matrix.SL2.Affine F) := by
  have hf (j : Bool) (e : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ≃*
      Matrix.PSL3.LinearThree.CoveredLocals.parabolic F j) :
      Nonempty (![L,residual H] i ≃* Matrix.SL2.Affine F) := by
    obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hTH hp F hm hF i j e).2.1
    cases j
    · exact ⟨a.trans (Matrix.PSL3.LinearThree.lineLocalEquivAffine F)⟩
    · exact ⟨a.trans (Matrix.PSL3.LinearThree.pointLocalEquivAffine F)⟩
  rcases he with he | he <;> obtain ⟨e⟩ := he <;> fin_cases i
  · exact hf true e.left
  · exact hf false e.right
  · exact hf false e.left
  · exact hf true e.right

/-- The literal core and Sylow orders in the nonmaximal linear row. The full
Borel remains unchanged; its two-core S has index two in the original T. -/
theorem Preparation.linear_nonmaximal_core_geometry
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    m = 2 ∧ n = 2 ∧ Nat.card F = 4 ∧
      (∀ i : Fin 2, IsElementaryAbelian 2 (pCore 2 (![L,residual H] i)) ∧
        Nat.card (pCore 2 (![L,residual H] i)) = 16) ∧
      (normalizer (L : Set G)).pCoreIn 2 = L.pCoreIn 2 ∧
      normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G) ∧
      centralizer (L.pCoreIn 2 : Set G) = L.pCoreIn 2 ∧
      Nat.card T = 128 ∧ Nat.card (sourceS L H) = 64 ∧
      (sourceS L H).relIndex (T : Subgroup G) = 2 := by
  obtain ⟨hmn, hcases⟩ := d.linear_maximal_or_exceptional h hH hp F hm hF he
  obtain ⟨hn,J,hJ,hKJ,hblock⟩ := hcases.resolve_left hnonmax
  have hm2 : m = 2 := hmn.trans hn
  have hF4 : Nat.card F = 4 := by simpa only [hm2, Nat.reducePow] using hF
  have hTH := hH.1.1.2
  have hcores (i : Fin 2) : IsElementaryAbelian 2 (pCore 2 (![L,residual H] i)) ∧
      Nat.card (pCore 2 (![L,residual H] i)) = 16 := by
    obtain ⟨e⟩ := linear_factor_affine d h hTH hp F hm hF he i
    let a := ChapterC.SL2Affine.coreEquiv e
    refine ⟨IsElementaryAbelian.of_injective a.symm.toMonoidHom a.symm.injective,?_⟩
    rw [← Nat.card_congr a.toEquiv]
    change Nat.card (Fin 2 → F) = 16
    simp only [Nat.card_fun, Nat.card_fin,hF4]
    norm_num
  have hcoreL : IsElementaryAbelian 2 (pCore 2 L) ∧ Nat.card (pCore 2 L) = 16 := hcores 0
  have hcoreK : IsElementaryAbelian 2 (pCore 2 (residual H)) ∧
      Nat.card (pCore 2 (residual H)) = 16 := hcores 1
  have hcoreM : (normalizer (L : Set G)).pCoreIn 2 = L.pCoreIn 2 := by
    let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊔ (T : Subgroup G)
    have hYL : Y ≤ normalizer (L : Set G) := by
      apply sup_le _ h.sylow_normalizes
      exact (normal_subgroupOf_iff_le_normalizer
        (show L ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 from
          le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hTH).local_normal_in_parabolic 0)
    have hc := d.parabolic_sylow_core_eq_of_comparison h hTH hp (.linear F m hm hF he) 0
    exact le_antisymm
      ((Chapter3.twoCore_le_of_sylow_le T (show (T : Subgroup G) ≤ Y from le_sup_right)
        hYL).trans_eq hc)
      (pCoreIn_mono_of_normalizes L.le_normalizer le_rfl)
  have hUne : L.pCoreIn 2 ≠ ⊥ := by
    intro hz
    have hh := card_map_of_injective (K := pCore 2 L) L.subtype_injective
    change Nat.card (L.pCoreIn 2) = Nat.card (pCore 2 L) at hh
    rw [hz,card_bot,hcoreL.2] at hh
    omega
  have hNU : normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G) := by
    have hle := normalizer_le_normalizer_characteristic_image L (pCore 2 L)
    exact le_antisymm (h.maximal.2 ⟨_,hUne,isPGroup_pCoreIn 2 L,rfl⟩ hle) hle
  have hCU : centralizer (L.pCoreIn 2 : Set G) = L.pCoreIn 2 := by
    apply le_antisymm
    · have hchar := Chapter1.mem_He_iff.mpr
        (h.qtke.evenCharacteristic T _ h.maximal h.sylow_normalizes)
      change normalizer (L : Set G) ⊓
        centralizer ((normalizer (L : Set G)).pCoreIn 2 : Set G) ≤
        (normalizer (L : Set G)).pCoreIn 2 at hchar
      rw [hcoreM] at hchar
      exact fun x hx => hchar ⟨hNU ▸ Subgroup.centralizer_le_normalizer _ hx,hx⟩
    · let := hcoreL.1
      let : IsMulCommutative (L.pCoreIn 2) :=
        inferInstanceAs (IsMulCommutative ((pCore 2 L).map L.subtype))
      exact fun x hx => mem_centralizer_iff.mpr (fun y hy => setLike_mul_comm hy hx)
  obtain ⟨hTJ,_,_,_,_,_,_,hJcard⟩ := d.linear_exceptional_local h hH hp F hm hF he hJ hKJ
  have hTcard : Nat.card T = 128 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hTJ).toEquiv]
    change Nat.card (T.subtype hTJ) = 128
    rw [(T.subtype hTJ).card_eq_multiplicity,hJcard]
    decide +kernel
  have hKcard : Nat.card (residual H) = 960 := by
    obtain ⟨_,_,_,_,_,_,hb,_⟩ := (d.linear_amalgam_blocks h hTH hp F hm hF he).2.2
    rw [hn] at hb
    obtain ⟨E,_,_,hE,⟨e⟩⟩ := hb
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hE
    have hq : Nat.card (residual H ⧸ pCore 2 (residual H)) = 60 := by
      rw [Nat.card_congr (e.trans a).toEquiv,nat_card_alternatingGroup]
      norm_num
    rw [← (pCore 2 (residual H)).card_mul_index,index_eq_card,hcoreK.2,hq]
  have hScard : Nat.card (sourceS L H) = 64 := by
    have hs := d.sylow 1
    change ∃ P : Sylow 2 (residual H), (P : Subgroup (residual H)).map (residual H).subtype =
      sourceS L H ⊓ residual H at hs
    obtain ⟨P,hP⟩ := hs
    have hSK : sourceS L H ≤ residual H := d.linear_sourceS_le_factors h hTH hp F hm hF he 1
    change (P : Subgroup (residual H)).map (residual H).subtype = sourceS L H ⊓ residual H at hP
    rw [inf_eq_left.mpr hSK] at hP
    rw [←hP,card_map_of_injective (residual H).subtype_injective,P.card_eq_multiplicity,hKcard]
    decide +kernel
  refine ⟨hm2,hn,hF4,hcores,hcoreM,hNU,hCU,hTcard,hScard,?_⟩
  have hc := ((sourceS L H).subgroupOf (T : Subgroup G)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (sourceS_le_sylow h.sylow_normalizes hTH)).toEquiv,hScard,hTcard] at hc
  change 64 * (sourceS L H).relIndex (T : Subgroup G) = 128 at hc
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
