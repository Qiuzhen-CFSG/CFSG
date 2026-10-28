module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.LinearThreeStarGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.ParabolicDescent
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedNormalizerAction
public import Theory.GroupAction.ModelQuotientAction
public import Theory.Representation.SL3QuotientParabolics
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# The two actual linear-three B.5 rows in the original rank-two argument

The original hypotheses normalize the component and its radical. Their
actual action on the star module preserves its moved space and central
quotient. Natural or doubled-natural coordinates therefore give compatible
module automorphisms. The two invariant flags lift along the literal star
projection to proper generating parabolics, contradicting proper-I induction
for every field larger than two. The remaining binary field gives PSL3(2).

This is the specialized source 15.3.20 route needed by 15.3.13, printed
pp.1125–1128. It uses the original B.5 rows directly and does not assume
C.1.32 block reconstruction or identify the star quotient with a core quotient.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)
include hG hempty hM hu hmany hI htwo hf hproper

theorem source_15_3_20_linearThree_row_large :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (F : BinaryField), 1 < F.degree →
      ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (linearNatural F 3) → False := by
  intro C J hCJ s F hlarge e
  let eStar := (subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv
  obtain ⟨hnL,hnR,hsol,T,hT⟩ := linearThree_star_source_geometry
    hG d hempty hM hu hmany hI htwo hf c F.card_eq hlarge eStar
  let A := d.Yplus ⊔ d.S
  let q := starMovedProjection hCJ e.groupEquiv
  have hq : Function.Surjective q := starMovedProjection_surjective hCJ e.groupEquiv
  obtain ⟨α,heq,himpl⟩ := EquivariantLift.model_action c.L A q hq hnL (linearNatural F 3)
    (fun a => starMovedSection_model_intertwiner hCJ s e a.val (hnL a.property) (hnR a.property))
  let : Group.IsSolvable A := hsol
  have hSA : (T : Subgroup c.L).map c.L.subtype ≤ A := by
    rw [hT,subgroupOf_map_subtype]
    exact inf_le_left.trans le_sup_right
  have hF : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hlarge
  have him (a : A) : ∃ b : (Fin 3 → F.Carrier) ≃+ (Fin 3 → F.Carrier),
      ∀ g v, b (g.val.mulVec v) = (α a g).val.mulVec (b v) := by
    obtain ⟨b,hb⟩ := himpl a
    exact ⟨b.toAddEquiv,hb⟩
  obtain ⟨P,Q,hP,hQ,hgen,hnP,hnQ,hbase⟩ :=
    SL3NaturalFlagInvariant.exists_lifted_parabolics c.L A q hq hnL α heq him hF T hSA
  have hS := (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI).sylow
  exact source_15_3_20_of_generating_parabolics d hI hS hf c hproper
    P Q hP hQ hgen hnP hnQ hbase

theorem source_15_3_20_doubleThree_row_large :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (F : BinaryField), 1 < F.degree →
      ActionEquiv (s.space.toRepresentation.comp (C.subgroupOf J).subtype)
        (repeated (linearNatural F 3) 2) → False := by
  intro C J hCJ s F hlarge e
  let eStar := (subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv
  obtain ⟨hnL,hnR,hsol,T,hT⟩ := linearThree_star_source_geometry
    hG d hempty hM hu hmany hI htwo hf c F.card_eq hlarge eStar
  let A := d.Yplus ⊔ d.S
  let q := starMovedProjection hCJ e.groupEquiv
  have hq : Function.Surjective q := starMovedProjection_surjective hCJ e.groupEquiv
  obtain ⟨α,heq,himpl⟩ := EquivariantLift.model_action c.L A q hq hnL (repeated (linearNatural F 3) 2)
    (fun a => starMovedSpace_model_intertwiner hCJ s e a.val (hnL a.property) (hnR a.property))
  let : Group.IsSolvable A := hsol
  have hSA : (T : Subgroup c.L).map c.L.subtype ≤ A := by
    rw [hT,subgroupOf_map_subtype]
    exact inf_le_left.trans le_sup_right
  have hF : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hlarge
  have him (a : A) : ∃ b : (Fin 2 → Fin 3 → F.Carrier) ≃ₗ[ZMod 2] (Fin 2 → Fin 3 → F.Carrier),
      ∀ g v, b (fun i => g.val.mulVec (v i)) = fun i => (α a g).val.mulVec (b v i) := by
    obtain ⟨b,hb⟩ := himpl a
    exact ⟨b,hb⟩
  obtain ⟨P,Q,hP,hQ,hgen,hnP,hnQ,hbase⟩ :=
    SL3NaturalFlagInvariant.exists_lifted_repeated_parabolics c.L A q hq hnL α heq (by decide : 0 < 2)
      him hF T hSA
  have hS := (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI).sylow
  exact source_15_3_20_of_generating_parabolics d hI hS hf c hproper
    P Q hP hQ hgen hnP hnQ hbase

omit hG hempty hM hu hmany hI htwo hf hproper in
private noncomputable def binaryThree_of_degree_one (F : BinaryField) (hF : F.degree = 1) :
    SL(3,F.Carrier) ≃* PSL(3,ZMod 2) := by
  let := Fintype.ofFinite F.Carrier
  have hc : Fintype.card F.Carrier = 2 := by
    rw [←Nat.card_eq_fintype_card,F.card_eq,hF]
    rfl
  let a : F.Carrier ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F.Carrier Nat.prime_two hc).symm
  exact (Atlas.fieldEquivSL 3 a).trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)).symm

/-- Every actual natural linear-three row leaves exactly the binary degree-three
model required by the source quotient assembly. -/
theorem source_linearThree_row_binary :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (F : BinaryField),
      ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (linearNatural F 3) →
        Nonempty (C ≃* PSL(3,ZMod 2)) := by
  intro C J hCJ s F e
  by_cases hn : 1 < F.degree
  · exact (source_15_3_20_linearThree_row_large hG d hempty hM hu hmany hI htwo hf c hproper
      hCJ s F hn e).elim
  · have hdeg : F.degree = 1 := by have := F.degree_pos; omega
    exact ⟨((subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv).trans (binaryThree_of_degree_one F hdeg)⟩

/-- The doubled-natural B.5 row has the same literal binary star endpoint. -/
theorem source_doubleThree_row_binary :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (F : BinaryField),
      ActionEquiv (s.space.toRepresentation.comp (C.subgroupOf J).subtype)
        (repeated (linearNatural F 3) 2) → Nonempty (C ≃* PSL(3,ZMod 2)) := by
  intro C J hCJ s F e
  by_cases hn : 1 < F.degree
  · exact (source_15_3_20_doubleThree_row_large hG d hempty hM hu hmany hI htwo hf c hproper
      hCJ s F hn e).elim
  · have hdeg : F.degree = 1 := by have := F.degree_pos; omega
    exact ⟨((subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv).trans (binaryThree_of_degree_one F hdeg)⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
