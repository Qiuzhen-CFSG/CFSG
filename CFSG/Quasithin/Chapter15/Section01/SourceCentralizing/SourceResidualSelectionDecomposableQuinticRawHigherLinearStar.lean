module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherLinear
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCohomology
public import Theory.Quasithin.NormalTwoQuotient
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-! The actual core maps to both the star and normalizer images. Their
central-quotient equivalences preserve the prescribed PSL3 field without
identifying the images or discarding a possible cubic kernel. The original
B.5 classifier and its proved linear-row restrictions then exclude the star. -/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

private theorem raw_projective_degree_eq (F E : BinaryField)
    (e : PSL(3,F.Carrier) ≃* PSL(3,E.Carrier)) : F.degree = E.degree := by
  let S : Sylow 2 PSL(3,F.Carrier) := Classical.choice inferInstance
  have hF := Matrix.PSL3.LinearThree.card_center_sylow F.Carrier F.degree_pos F.card_eq S
  have hE := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv E.Carrier
    E.degree_pos E.card_eq e S
  exact Nat.pow_right_injective (by decide : 1 < 2) (hF.symm.trans hE)

private theorem raw_projective_not_binary (F : BinaryField) (hn : 1 < F.degree)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : PSL(3,F.Carrier) ≃* SL(d,ZMod 2)) : False := by
  let S : Sylow 2 SL(d,ZMod 2) := Classical.choice inferInstance
  have hc := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F.Carrier
    F.degree_pos F.card_eq e.symm S
  have hb := BinaryLinear.sl_sylow_center_card_le_two (by rcases hd with rfl | rfl <;> decide) S
  rw [hc] at hb
  have hl : 2 < 2^F.degree :=
    (show 2 = 2^1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
  omega

private theorem raw_source_not_projective_three
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {B : Subgroup D} [IsQuasisimple B]
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ B)
    (hsq : IsSQTK KnownSimple.IsKnownSimple D) (hff : IsFFModule ρ)
    (F : BinaryField) (hn : 1 < F.degree) (eq : (B ⧸ center B) ≃* PSL(3,F.Carrier))
    (hl : ∀ E : BinaryField, ActionEquiv (c.sectionData.action.comp B.subtype)
      (linearNatural E 3) → E.degree = 1)
    (hd : ∀ E : BinaryField, ActionEquiv (c.sectionData.space.toRepresentation.comp B.subtype)
      (repeated (linearNatural E 3) 2) → E.degree = 1) : False := by
  have hb {d : ℕ} (hdim : d = 4 ∨ d = 5) (a : B ≃* SL(d,ZMod 2)) : False := by
    have hdz : 0 < d := by rcases hdim with rfl | rfl <;> decide
    let e := QuotientGroup.congr _ _ a (Theory.GroupTheory.FixedElementary.map_center a)
    let eb := (QuotientGroup.quotientMulEquivOfEq
      (BinaryLinear.OuterCyclic.binary_center_eq_bot hdz)).trans QuotientGroup.quotientBot
    exact raw_projective_not_binary F hn hdim (eq.symm.trans (e.trans eb))
  cases c.clause_one with
  | irreducible hi hf hirr _ _ =>
    have hff' : IsFFModule c.sectionData.action := by
      obtain ⟨A,hA⟩ := hff
      exact ⟨A,IrreducibleBranch.moved_offender c.sectionData hA⟩
    have hratio : quadraticRatio c.sectionData.action ≤ 2 :=
      ((isFFModule_iff_quadraticRatio_le_one _).mp hff').trans (by norm_num)
    let hs : ChapterK.Linear.Recognition.SourceHypothesis KnownSimple.IsKnownSimple
        c.sectionData.action B :=
      ⟨inferInstance,inferInstance,hsq,c.fitting_eq.symm,inferInstance,hf,hirr,
        (cubicRatio_le_quadraticRatio _).trans hratio⟩
    obtain ⟨a⟩ := ChapterK.Linear.Recognition.SourceFF.naturalSourceInput_of_quotient_ff
      hs eq hff'
    have he := hl F a.natural
    omega
  | doubleThree E _ a _ _ =>
    let ep := QuotientGroup.congr _ _ a.groupEquiv
      (Theory.GroupTheory.FixedElementary.map_center a.groupEquiv)
    have he := raw_projective_degree_eq F E (eq.symm.trans ep)
    have hb := hd E a
    omega
  | naturalDual d hdim _ ha =>
    obtain ⟨a⟩ := ha
    exact hb hdim a.groupEquiv
  | repeatedNatural d r hdim _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact hb hdim a.groupEquiv

variable {G : Type*} [Group G] [Finite G]

/-- The original C.2.7 star cannot be a higher-field full SL3 group. Both
central comparison kernels are retained until passing to their exact
central quotients; the same original normalizer classifier supplies the
natural and doubled-natural field restrictions. -/
theorem PreparedChosenModule.raw_constrained_not_higher_linear_star
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
    (F : BinaryField) (hn : 1 < F.degree)
    (e : starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ≃* SL(3,F.Carrier)) : False := by
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
  let es := e.toMonoidHom.comp (coreToStar hi.normalizes)
  have hes : Function.Surjective es := e.surjective.comp (coreToStar_surjective hi.normalizes)
  let : IsSimpleGroup PSL(3,F.Carrier) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Nontrivial SL(3,F.Carrier) := (Matrix.PSL3.projection_surjective F.Carrier).nontrivial
  let eqI := (IsQuasisimple.centralQuotientEquiv ec hec).symm.trans
    (IsQuasisimple.centralQuotientEquiv es hes)
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
