module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.Recognition
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.LayerClosureHead
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank

/-!
# The central binary cover in the original A₅ overcomponent

The original contained-layer split, together with a quasisimple head
I/O₂(I), kills the entire two-core of the embedded block. We retain the
literal restricted quotient map: its kernel is exactly O₂(L), and its
image is A₅. No identification of U(L) with O₂(L) is used.

For the actual involution-centralizer component, A.3.6 supplies a bounded
alternative: this core and image conclusion holds, or I/O₂(I) has two-rank
one. Exclusion of that latter alternative still requires the original
geometry; it is not a consequence asserted here of the split module alone.

Source: Aschbacher–Smith 10.2.1, p.743, A.3.6, pp.43–45, and the
SL₂(5) possibility explicitly retained by C.1.13(c), pp.124–125.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- A quasisimple head kills the possible central binary lift in the original block. -/
theorem source_a5_overcomponent_core_of_quasisimple_head
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X)
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I)
    (hq : IsQuasisimple (I ⧸ pCore 2 I)) :
    let K := L.subgroupOf I
    let q := QuotientGroup.mk' (pCore 2 I)
    K.pCoreIn 2 ≤ pCore 2 I ∧ (q.subgroupMap K).ker = pCore 2 K ∧
      Nonempty (K.map q ≃* alternatingGroup (Fin 5)) := by
  let K := L.subgroupOf I
  let W := normalClosure ((blockU K).map K.subtype : Set I)
  let q := QuotientGroup.mk' (pCore 2 I)
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hK : IsAlternatingBlock K 5 := hL.of_mulEquiv (subgroupOfEquivOfLe hLI).symm
  obtain ⟨S,_,hSK⟩ := source_containing_component_sylow hLI hIX hI hS
  have hs := hK.normalClosure_layer_split K S hSK hU
  let := hq
  have hcore := hK.core_le_ambient_core_of_quasisimple_head K W le_normalClosure
    hs.2.2.2.1 hs.2.1
  have hk : (q.subgroupMap K).ker = pCore 2 K := by
    apply le_antisymm
    · apply le_sSup
      refine ⟨inferInstance,?_⟩
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    · intro k hk
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (k:I)).mpr
        (hcore (mem_map_of_mem K.subtype hk))
  obtain ⟨a⟩ := hK.2.2.quotient_iso
  exact ⟨hcore,hk,⟨(QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap K)
    (q.subgroupMap_surjective K)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans a)⟩⟩

private theorem head_quasisimple_or_rank_one
    {I X : Subgroup G} (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent)
    (hsq : IsSQTK KnownSimple.IsKnownSimple X) :
    IsQuasisimple (I ⧸ pCore 2 I) ∨ primeRank 2 (I ⧸ pCore 2 I) = 1 := by
  let Q := I ⧸ pCore 2 I
  have hsqI : IsSQTK KnownSimple.IsKnownSimple I :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hIX)).mp (hsq.subgroup (I.subgroupOf X))
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hsqI.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 I) pCore_isPGroup).trans
      (hsqI.stronglyQuasithin p hp ho)
  have htop : (⊤:Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using hI.subgroupOf_of_le le_rfl hIX
  let : Group.IsNilpotent (pCore 2 I) := pCore_isNilpotent
  have hbar : (⊤:Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 I)
  by_cases hc : fittingSubgroup (⊤:Subgroup Q) ≤ center (⊤:Subgroup Q)
  · left
    have hr : solvableRadical (⊤:Subgroup Q) = center (⊤:Subgroup Q) := le_antisymm
      (solvableRadical_le_center_of_fitting_le_center hc)
      (le_solvableRadical _ inferInstance
        (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm))
    let := hbar.perfect
    let := hbar.isSimpleGroup_quotient_solvableRadical
    let : IsQuasisimple (⊤:Subgroup Q) :=
      ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
    exact IsQuasisimple.of_mulEquiv topEquiv
  · right
    have hh := ChapterA.Section03.NoncentralFitting.two_rank_eq_one_of_noncentral
      hsqQ (pCore_quotient_pCore_eq_bot 2) hbar hc
    rwa [primeRank_equiv 2 (topEquiv : (⊤:Subgroup Q) ≃* Q)] at hh

/-- The actual involution centralizer supplies SQTK; only the rank-one head remains. -/
theorem source_a5_involution_overcomponent_core_or_two_rank_one
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {v : G} (hv : orderOf v = 2) {I : Subgroup G} (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({v}:Set G))
    (hI : (I.subgroupOf (centralizer ({v}:Set G))).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G))
      (centralizer ({v}:Set G)))
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I) :
    let K := L.subgroupOf I
    let q := QuotientGroup.mk' (pCore 2 I)
    (IsQuasisimple (I ⧸ pCore 2 I) ∧ K.pCoreIn 2 ≤ pCore 2 I ∧
      (q.subgroupMap K).ker = pCore 2 K ∧
      Nonempty (K.map q ≃* alternatingGroup (Fin 5))) ∨
        primeRank 2 (I ⧸ pCore 2 I) = 1 := by
  rcases head_quasisimple_or_rank_one hIX hI
    (D.simpleQTKE.involution_centralizer_sqtk hv) with hq | hr
  · exact Or.inl ⟨hq,source_a5_overcomponent_core_of_quasisimple_head
      D e hn hout hLI hIX hI hS hU hq⟩
  · exact Or.inr hr
end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
