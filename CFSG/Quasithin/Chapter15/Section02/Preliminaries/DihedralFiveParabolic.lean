module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveChiefKernel
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceFaithfulTriple
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.SpecificGroups.AlternatingFiveCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.GroupTheory.SylowSmallCoreQuotient
/-!
# The actual rank-one pairs in the marked-five quotient branches

The order-five Case-II residual gives L₀=YRc with quotient D₁₀ or Sz(2),
Sylow subgroup Rc, and Borel Rc. For H/O₂(H)=S₃ take K=H. For
H/O₂(H)=S₅ take the literal embedded two-residual K=O²(H); its quotient
by its own two-core is A₅, and KT=H.

The Borel of K lies in the original maximal subgroup H∩M. Its normal
Sylow part gives the precise identity H∩M=N_H(T∩K); in particular no
blanket identification of a unique maximal Sylow overgroup with N_H(T)
is used. The original residual normalizer control supplies cross-actions,
YT uniqueness proves the generated two-core is trivial, and the actual
Sylow intervals give characteristic two. Thus all six original F.1.1
clauses hold, with H retained as the second parabolic.

The use of K in the symmetric-five case makes explicit the correction
needed in the printed F.1.1 invocation: S₅ itself is not a rank-one
quotient in F.1.1(c). Rank-two recognition and the final exclusions in
15.2.8 remain separate source obligations.

Source: Aschbacher--Smith, original 15.2.8, printed pp.1109--1110,
and F.1.1--F.1.9, printed pp.259--261.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem intersection_le_centralizer_sylow (T : Sylow 2 G)
    {M V H : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hV : PreparedChosenModule T M V) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    H ⊓ M ≤ (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  have hTI : (T : Subgroup G) ≤ H ⊓ M := le_inf hH.1.1.2 hTM
  have hs := congrArg (Subgroup.map (H ⊓ M).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTI))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI,
    ←MonoidHom.range_eq_map,range_subtype] at hs
  rw [←hs]
  exact sup_le_sup (le_inf ((map_subtype_le _).trans inf_le_right)
    (hV.intersection_residual H hH)) le_rfl

private theorem small_borel_eq {L S R : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 R L) (hSL : S ⊓ L = R)
    (hc : Nat.card (L ⧸ pCore 2 L) = 6 ∨ Nat.card (L ⧸ pCore 2 L) = 10 ∨
      Nat.card (L ⧸ pCore 2 L) = 20) : ChapterF.Source.borel L S = R := by
  obtain ⟨P,hP⟩ := hSyl
  have hn := (sylow_normalizer_small_core_quotient P hc).1
  have hPL : R.subgroupOf L = (P : Subgroup L) := by
    rw [←hP]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hm := congrArg (Subgroup.map L.subtype) hn
  change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _ at hm
  rw [←hPL,←subgroupOf_normalizer_eq (hP ▸ map_subtype_le _),
    subgroupOf,map_comap_eq,range_subtype] at hm
  change L ⊓ normalizer (R : Set G) = (R.subgroupOf L).map L.subtype at hm
  rw [map_subgroupOf_eq_of_le (hP ▸ map_subtype_le _)] at hm
  simpa only [ChapterF.Source.borel,hSL,inf_comm] using hm

/-- A normal rank-one factor has its literal Sylow Borel in the original
unique maximal overgroup. The Sylow normalizer of H itself is not used. -/
private theorem rankOne_borel_le_intersection (T : Sylow 2 G)
    {M H K : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ K) K)
    (hq : ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K)) :
    ChapterF.Source.borel K (T : Subgroup G) ≤ H ⊓ M := by
  obtain ⟨P,hP⟩ := hSyl
  have hf := ChapterF.Source.rankOneBorelFacts_of_sylow K (T : Subgroup G) P hP
    (ChapterF.Source.rankOneSylowFacts_of_rankOneQuotient hq P)
  let N := H ⊓ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)
  have hTN : (T : Subgroup G) ≤ N := le_inf hH.1.1.2
    (le_normalizer_inf (T : Subgroup G).le_normalizer (hH.1.1.2.trans hHK))
  have hNH : N < H := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hK : K ≤ ChapterF.Source.borel K (T : Subgroup G) :=
      le_inf le_rfl (hKH.trans (he.symm.le.trans inf_le_right))
    exact (not_le_of_gt hf.proper) hK
  have hNM := (Chapter3.HStar.hasUniqueMaximalOver T hTM hH).le_maximal
    ⟨(Chapter3.HStar.unique_maximal T hTM hH).1,
      (Chapter3.HStar.unique_maximal T hTM hH).2.1⟩ hTN hNH
  exact (le_inf (inf_le_left.trans hKH) inf_le_right).trans hNM


private theorem rankOne_of_permThree {D : Type*} [Group D]
    (e : D ≃* Equiv.Perm (Fin 3)) : ChapterF.Source.IsRankOneModel D := by
  apply ChapterF.Source.IsRankOneModel.linear 1 (by decide)
  refine ⟨ZMod 2,inferInstance,inferInstance,by simp,?_⟩
  exact ⟨e.trans (SLTwoPermThree.sl2Two_equiv_perm_three.some.symm.trans
    Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two)⟩

private theorem rankOne_of_altFive {D : Type*} [Group D]
    (e : D ≃* alternatingGroup (Fin 5)) : ChapterF.Source.IsRankOneModel D := by
  apply ChapterF.Source.IsRankOneModel.linear 2 (by decide)
  refine ⟨GaloisField 2 2,inferInstance,inferInstance,?_,
    ⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
  rw [GaloisField.card 2 2 (by decide)]



/-- The original maximal subgroup normalizes the Sylow part of the normal
rank-one factor, which may be smaller than the Sylow subgroup of H. -/
private theorem rankOne_intersection_normalizer (T : Sylow 2 G)
    {M H K : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ K) K)
    (hq : ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K)) :
    H ⊓ M = H ⊓ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hB := rankOne_borel_le_intersection T hTM hH hKH hHK hSyl hq
  obtain ⟨P,hP⟩ := hSyl
  have hf := ChapterF.Source.rankOneBorelFacts_of_sylow K (T : Subgroup G) P hP
    (ChapterF.Source.rankOneSylowFacts_of_rankOneQuotient hq P)
  have hBK : (H ⊓ M) ⊓ K = ChapterF.Source.borel K (T : Subgroup G) := by
    apply le_antisymm ?_ (le_inf hB inf_le_left)
    apply hf.unique_maximal _
      (le_inf (le_inf (inf_le_left.trans hH.1.1.2) (inf_le_left.trans hTM)) inf_le_right)
    apply lt_of_le_of_ne inf_le_right
    intro he
    apply hH.1.2
    rw [←hKT]
    exact sup_le (he.symm.le.trans (inf_le_left.trans inf_le_right)) hTM
  have hnorm : H ⊓ M ≤ normalizer (ChapterF.Source.borel K (T : Subgroup G) : Set G) := by
    rw [←hBK]
    exact le_normalizer_inf (H ⊓ M).le_normalizer (inf_le_left.trans hHK)
  have hc := hnorm.trans (normalizer_le_normalizer_characteristic_image
    (ChapterF.Source.borel K (T : Subgroup G)) (pCore 2 (ChapterF.Source.borel K (T : Subgroup G))))
  change H ⊓ M ≤ normalizer (ChapterF.Source.twoCore
    (ChapterF.Source.borel K (T : Subgroup G)) : Set G) at hc
  rw [hf.twoCore_eq] at hc
  refine le_antisymm (le_inf inf_le_left hc) ?_
  let N := H ⊓ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)
  have hTN : (T : Subgroup G) ≤ N := le_inf hH.1.1.2
    (le_normalizer_inf (T : Subgroup G).le_normalizer (hH.1.1.2.trans hHK))
  have hNH : N < H := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    exact (not_le_of_gt hf.proper) (le_inf le_rfl (hKH.trans (he.symm.le.trans inf_le_right)))
  exact le_inf inf_le_left (Chapter3.HStar.proper_overgroup_le T hH hTN hNH)

section ChosenFive
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype)) {m : ℕ}
    (hp : PrimeDimensionOptions 5 m) (hd : DihedralMarking l 5 m)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hJ hu hmany l hp hd hH

private theorem marked_five_rankOne_pair {K : Subgroup G}
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ K) K)
    (hq : ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K)) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let R := (M ⊓ Mc).pCoreIn 2
    let L := ![Y ⊔ R,K]
    ChapterF.Source.HypothesisF11 L (T : Subgroup G) ∧
      ChapterF.Source.borel (Y ⊔ R) (T : Subgroup G) = R ∧
      ChapterF.Source.parabolic L (T : Subgroup G) 1 = H ∧
      H ⊓ M = H ⊓ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) ∧
      (T : Subgroup G) ⊔ ChapterF.Source.borel (Y ⊔ R) (T : Subgroup G) = T := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let R := (M ⊓ Mc).pCoreIn 2
  let L₀ := Y ⊔ R
  have hRT : R ≤ (T : Subgroup G) := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
    have hTMc : (T : Subgroup G) ≤ Mc := by
      intro t ht
      apply hMc.2
      intro z hz
      exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
    have hTI := le_inf hM.1.2 hTMc
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI] using
      pCoreIn_le_sylow (M ⊓ Mc) (T.subtype hTI)
  have hYL : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hLM : L₀ ≤ M := sup_le hYL (hRT.trans hM.1.2)
  have hSyl₀ : Chapter1.IsSylowIn 2 R L₀ :=
    source_dihedral_five_intersection_core_sylow hG T hempty hM hJ hu hmany hV l hp hd
  have hTL : (T : Subgroup G) ⊓ L₀ = R := (Chapter1.isSylowIn_iff.mp hSyl₀).2.2 _
    (T.isPGroup'.to_le inf_le_left) (le_inf hRT le_sup_right) inf_le_right
  have hquot := source_dihedral_five_join_quotient hG T hempty hM hJ hu hmany hV l hp hd
  have hB₀ : ChapterF.Source.borel L₀ (T : Subgroup G) = R := by
    apply small_borel_eq hSyl₀ hTL
    rcases hquot with he₀ | he₀
    · obtain ⟨e⟩ := he₀
      exact Or.inr (Or.inl (by rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]))
    · obtain ⟨e⟩ := he₀
      exact Or.inr (Or.inr ((Nat.card_congr e.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card))
  have hB₁ := rankOne_borel_le_intersection T hM.1.2 hH hKH hHK hSyl hq
  have hTN : (T : Subgroup G) ≤ normalizer (L₀ : Set G) := le_sup_right.trans
    (source_chosen_centralizer_sylow_normalizes_residual T hM.1.2 hu hV).2
  have hB₁N : ChapterF.Source.borel K (T : Subgroup G) ≤ normalizer (L₀ : Set G) :=
    (hB₁.trans (intersection_le_centralizer_sylow T hM.1.2 hV hH)).trans
      (source_chosen_centralizer_sylow_normalizes_residual T hM.1.2 hu hV).2
  have hP₁ : ChapterF.Source.parabolic ![L₀,K] (T : Subgroup G) 1 = H := by
    change K ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel L₀ (T : Subgroup G) = H
    rw [hKT,hB₀,sup_eq_left.mpr (hRT.trans hH.1.1.2)]
  have hgen : ChapterF.Source.generated ![L₀,K] (T : Subgroup G) =
      (Y ⊔ (T : Subgroup G)) ⊔ H := by
    change (Y ⊔ R) ⊔ K ⊔ (T : Subgroup G) = (Y ⊔ (T : Subgroup G)) ⊔ H
    apply le_antisymm
    · exact sup_le (sup_le (sup_le (le_sup_left.trans le_sup_left)
        (hRT.trans (le_sup_right.trans le_sup_left))) (hKH.trans le_sup_right))
        (le_sup_right.trans le_sup_left)
    · exact sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) le_sup_right)
        (hKT.symm.le.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  have huni := source_dihedral_five_residual_sylow_unique hG T hempty hM hJ hu hmany hV l hp hd
  have hfree : pCore 2 (ChapterF.Source.generated ![L₀,K] (T : Subgroup G)) = ⊥ := by
    rw [hgen]
    apply twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup _ H M ?_ hH.1.2
    intro N hN hYN
    exact Set.mem_singleton_iff.mp (huni ▸
      (show N ∈ maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) from ⟨hN,hYN⟩))
  refine ⟨?_,hB₀,hP₁,
    rankOne_intersection_normalizer T hM.1.2 hH hKH hHK hKT hSyl hq,?_⟩
  swap
  · rw [hB₀]
    exact sup_eq_left.mpr hRT
  refine ⟨inferInstance,T.isPGroup',?_,?_,?_,?_,hfree,?_⟩
  · intro i
    fin_cases i
    · exact hTN
    · exact hH.1.1.2.trans hHK
  · intro i
    fin_cases i
    · exact hTL.symm ▸ hSyl₀
    · exact hSyl
  · intro i
    fin_cases i
    · exact hquot.elim ChapterF.Source.IsRankOneModel.dihedral
        (ChapterF.Source.IsRankOneModel.suzuki 0)
    · exact hq
  · intro i
    fin_cases i
    · exact hB₁N
    · change ChapterF.Source.borel L₀ (T : Subgroup G) ≤ normalizer (K : Set G)
      rw [hB₀]
      exact hRT.trans (hH.1.1.2.trans hHK)
  · intro i
    fin_cases i
    · apply generalizedFitting_eq_pCore_of_sylow_overgroup T _ M
        (le_sup_right.trans le_sup_left)
        (sup_le (sup_le hLM hM.1.2) (hB₁.trans inf_le_right))
      exact hG.evenCharacteristic T M hM.1.1 hM.1.2
    · change generalizedFitting (ChapterF.Source.parabolic ![L₀,K] (T : Subgroup G) 1) =
        pCore 2 (ChapterF.Source.parabolic ![L₀,K] (T : Subgroup G) 1)
      rw [hP₁]
      exact (source_centralizing_minimalParabolic hG T hM hJ H hH).2.2.2.2
/-- The marked-five S₃ branch gives the actual faithful (5,3) local pair.
Its second parabolic is precisely the original H. -/
theorem source_dihedral_five_symmetricThree_pair
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let R := (M ⊓ Mc).pCoreIn 2
    let L := ![Y ⊔ R,H]
    ChapterF.Source.HypothesisF11 L (T : Subgroup G) ∧
      ChapterF.Source.borel (Y ⊔ R) (T : Subgroup G) = R ∧
      ChapterF.Source.parabolic L (T : Subgroup G) 1 = H ∧
      H ⊓ M = H ⊓ normalizer (((T : Subgroup G) ⊓ H : Subgroup G) : Set G) ∧
      (T : Subgroup G) ⊔ ChapterF.Source.borel (Y ⊔ R) (T : Subgroup G) = T := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  apply marked_five_rankOne_pair hG T hempty hM hJ hu hmany hV l hp hd hH
    le_rfl H.le_normalizer (sup_eq_left.mpr hH.1.1.2) ?_ (rankOne_of_permThree he.some)
  refine ⟨T.subtype hTH,?_⟩
  have hint : (T : Subgroup G) ⊓ H = T := inf_eq_left.mpr hTH
  exact (map_subgroupOf_eq_of_le hTH).trans hint.symm

/-- The S₅ branch uses the actual O²(H) as its rank-one factor. Adjoining
T recovers H, retaining the full original parabolic and its two-core. -/
theorem source_dihedral_five_symmetricFive_pair
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let R := (M ⊓ Mc).pCoreIn 2
    let K := (pResidual 2 H).map H.subtype
    let L := ![Y ⊔ R,K]
    ChapterF.Source.HypothesisF11 L (T : Subgroup G) ∧
      ChapterF.Source.borel (Y ⊔ R) (T : Subgroup G) = R ∧
      ChapterF.Source.parabolic L (T : Subgroup G) 1 = H ∧
      H ⊓ M = H ⊓ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) ∧
      (T : Subgroup G) ⊔ ChapterF.Source.borel (Y ⊔ R) (T : Subgroup G) = T ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let K := (pResidual 2 H).map H.subtype
  let f := he.some.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := he.some.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ he.some.injective,QuotientGroup.ker_mk']
  let eR := equivMapOfInjective (pResidual 2 H) H.subtype H.subtype_injective
  let eA := MulEquiv.subgroupCongr (Equiv.Perm.twoResidual_eq_alternating (Fin 5))
  let eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ eR.symm (pCore_map_iso 2 eR.symm)).trans
      ((f.pResidualCoreQuotientEquiv hf (hk.symm ▸ pCore_isPGroup)).trans
        ((QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans
          ((QuotientGroup.quotientMulEquivOfEq alternatingGroup.five_twoCore_eq_bot).trans
            QuotientGroup.quotientBot)))
  have hKH : K ≤ H := map_subtype_le _
  have hHK : H ≤ normalizer (K : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pResidual 2 H).le_normalizer_map H.subtype
  have hKT : K ⊔ (T : Subgroup G) = H := by
    have h := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
    simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype] using h
  have hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ K) K :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype hTH,map_subgroupOf_eq_of_le hTH⟩ hKH
      (normal_subgroupOf_of_le_normalizer hHK).isSubnormal
  obtain ⟨hF,hB,hP,hN,hBT⟩ := marked_five_rankOne_pair hG T hempty hM hJ hu hmany hV l hp hd hH
    hKH hHK hKT hSyl (rankOne_of_altFive eK)
  exact ⟨hF,hB,hP,hN,hBT,⟨eK⟩⟩

end ChosenFive
end CFSG.Quasithin.Chapter15.Section02
