module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherLinearStar
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherLinearStar

/-! The actual seed-normalizer image has no higher SL3 field. Its own B5
conclusion and the proved natural/doubled-natural field restrictions are
used directly. The original seed, whole action kernel and component remain
unchanged; no C2.7-star identification or model callback is introduced. -/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The actual original normalizer image cannot be a higher-field SL3. -/
theorem PreparedChosenModule.raw_component_normalizer_not_higher_linear
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (F : BinaryField) (hn : 1 < F.degree) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H := L ⊔ (S ⊓ normalizer (L : Set G))
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let I := (L.subgroupOf H).map (QuotientGroup.mk' (centralizer (W : Set H)))
    I ≃* SL(3,F.Carrier) → False := by
  dsimp only
  intro e
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  let H := L ⊔ R
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let I := (L.subgroupOf H).map q
  let := h.elementary
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect hL.2
  let := hi.quasisimple
  have houtM : ¬L ≤ M := by
    intro hLM
    exact hi.outside (le_inf hL.1
      ((perfect_subgroup_centralizes_localModule hG T hempty hM hLM).trans
        (localModule_centralizer_le_partner T M hu)))
  obtain ⟨hr,_,hfit,hqi,hff,hIJ,c,hl,hd⟩ := h.raw_linear_source_rows_binary
    hG T hempty hM hJ hu hZ hZne hL hi.quasisimple hi.fitting hi.outside
  let := hr.elementary
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := offenderSubgroup ρ
  let B := I.subgroupOf J
  let i : B ≃* I := subgroupOfEquivOfLe hIJ
  let : IsQuasisimple I := hqi
  let : Nontrivial (I ⧸ center I) := IsQuasisimple.simple.toNontrivial
  let : Nontrivial I := (QuotientGroup.mk'_surjective (center I)).nontrivial
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv i.symm
  obtain ⟨f,ec,_,_,hf,hec,_,_⟩ := h.raw_component_normalizer_quotient
    hG T hM hJ hu hZ hZne hL hi.quasisimple hi.fitting hi.outside houtM
  let eqI := QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)
  let eqB := (QuotientGroup.congr _ _ i
    (Theory.GroupTheory.FixedElementary.map_center i)).trans eqI
  let : (L.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer inf_le_right)
  let : I.Normal := inferInstanceAs ((L.subgroupOf H).map q).Normal
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  have hsqL : IsSQTK KnownSimple.IsKnownSimple L :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hL.1)).mp
      (hsq.subgroup (L.subgroupOf (centralizer (Z1 : Set G))))
  have hsqI : IsSQTK KnownSimple.IsKnownSimple I :=
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      hsqL (ChapterA.Section02.IsSectionOf.of_surjective f hf)
  have hgen : I ⊔ (R.subgroupOf H).map q = ⊤ := by
    change (L.subgroupOf H).map q ⊔ (R.subgroupOf H).map q = ⊤
    rw [←Subgroup.map_sup,←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
    exact map_top_of_surjective q (QuotientGroup.mk'_surjective C)
  have hR : IsPGroup 2 R := T.isPGroup'.to_le
    (inf_le_left.trans (show S ≤ (T : Subgroup G) from inf_le_left))
  have htwo : IsPGroup 2 ((H ⧸ C) ⧸ I) :=
    isPGroup_quotient_of_sup_eq_top I ((R.subgroupOf H).map q) (hR.comap_subtype.map q) hgen
  have hHG : H ≤ centralizer (Z1 : Set G) := sup_le hL.1 (inf_le_left.trans inf_le_right)
  have hsqH : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp (hsq.subgroup (H.subgroupOf _))
  have hsqD : IsSQTK KnownSimple.IsKnownSimple (H ⧸ C) := by
    refine ⟨?_,hsqH.isKGroup.quotient C⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_le_of_normal_two_quotient I htwo p ho).trans
      (hsqI.stronglyQuasithin p hp ho)
  have hffJ : IsFFModule (ρ.comp J.subtype) := by
    obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
    exact ⟨A.subgroupOf J,(hA.subgroupOf ρ (hA.le_offenderSubgroup ρ)).isOffender _⟩
  exact raw_source_not_projective_three (ρ.comp J.subtype) c (hsqD.subgroup J) hffJ F hn eqB hl hd

end CFSG.Quasithin.Chapter15.Section01
