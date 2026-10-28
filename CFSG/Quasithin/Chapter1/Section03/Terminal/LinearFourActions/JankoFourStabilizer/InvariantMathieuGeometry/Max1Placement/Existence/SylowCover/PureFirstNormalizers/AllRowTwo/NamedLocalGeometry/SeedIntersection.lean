module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.IncidenceCount

/-!
# Exact native kernel intersections of F occurrences

The seven checked seed words supply 128 distinct points in the intersection
of a literal F conjugate with the original max2 point core. The extraspecial
abelian size bound gives the matching upper bound, proving exhaustiveness
without an unchecked finite centralizer calculation. Every word in the actual
max2 source preserves that core, so the same description transports to all
word-defined F occurrences. The final membership equivalence applies directly
to the shared native words used by the finite rows.

This certifies the native intersection needed by finite F-incidence arguments;
it does not assert that a proposed list exhausts the ambient F occurrences.
Source context: Kleidman--Wilson (1988), Section 2.1, pp.488--489; the native
ATLAS words and their attribution are retained in the imported certificates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
open ElementaryNormalizerCover FiniteConfigurations
open Cardinality.LocalInvolutionCensus Cardinality.LocalInvolutionCensus.Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
attribute [local irreducible] modelGroup matrixA matrixB

@[expose] def sourceCore : Subgroup Model := firstCore.map (MulAut.conj h).toMonoidHom
@[expose] def seedF : Subgroup Model := LinearFive.F.map (MulAut.conj BridgeCertificates.bridge⁻¹).toMonoidHom
@[expose] def seedIntersection : Subgroup Model := sourceCore ⊓ seedF

private theorem kernel_mem_sourceCore (i : Fin 8192) : nativeWord i ∈ sourceCore := by
  have hm : eH (localKernelProduct i) ∈ firstCore := by
    rw [← firstKernel_eq_firstCore]
    exact (mem_firstKernel_iff _).mpr ⟨i,rfl⟩
  have hh := mem_map_of_mem (MulAut.conj h).toMonoidHom hm
  simpa only [sourceCore,nativeWord,localKernelProduct,eH_sourceSubgroupEquivLocal,
    MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply,mul_assoc,
    mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh

private theorem sourceCore_extraspecial : IsExtraspecial 2 sourceCore :=
  IsExtraspecial.of_mulEquiv
    (firstCore.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective)
    firstCore_extraspecial

private theorem sourceCore_card : Nat.card sourceCore = 8192 := by
  rw [sourceCore,card_map_of_injective (MulAut.conj h).injective]
  exact (card_map_of_injective InvolutionCentralizers.First.centralizer.subtype_injective).trans
    InvolutionCentralizers.First.centralizer_twoCore_card

private theorem seedIntersection_elementary : IsElementaryAbelian 2 seedIntersection := by
  let := LinearFive.F_elementary
  let : IsElementaryAbelian 2 seedF := IsElementaryAbelian.map _
  exact IsElementaryAbelian.of_le (show seedIntersection ≤ seedF from inf_le_right)

private theorem seedIntersection_card_le : Nat.card seedIntersection ≤ 128 := by
  let := sourceCore_extraspecial
  let := seedIntersection_elementary
  let E := seedIntersection.subgroupOf sourceCore
  have hle : seedIntersection ≤ sourceCore := inf_le_left
  have hc : Nat.card E = Nat.card seedIntersection :=
    Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hle
  have hb := extraspecial_prime_abelian_card_sq_le_any (p := 2) E
  rw [hc,sourceCore_card] at hb
  nlinarith

private theorem seedCoordinate_injective : Function.Injective seedCoordinate := by decide +kernel

private theorem seedCoordinate_mem_intersection (i : Fin 128) :
    nativeWord (seedCoordinate i) ∈ seedIntersection :=
  ⟨kernel_mem_sourceCore _,seedCoordinate_mem i⟩

private def seedEmbedding : Fin 128 → seedIntersection :=
  fun i => ⟨nativeWord (seedCoordinate i),seedCoordinate_mem_intersection i⟩

private theorem seedEmbedding_injective : Function.Injective seedEmbedding := by
  intro i j hij
  apply seedCoordinate_injective
  apply kernelProduct_injective
  exact Subtype.ext (congrArg (fun x : seedIntersection => (x : Model)) hij)

/-- The seed F occurrence saturates the abelian bound in the native point core. -/
theorem seedIntersection_card : Nat.card seedIntersection = 128 := by
  apply le_antisymm seedIntersection_card_le
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective seedEmbedding seedEmbedding_injective

/-- The listed 128 words exhaust the actual intersection, by its extraspecial bound. -/
theorem mem_seedIntersection_iff (x : Model) : x ∈ seedIntersection ↔
    ∃ i : Fin 128, nativeWord (seedCoordinate i) = x := by
  have hs := (seedEmbedding_injective.bijective_of_nat_card_le
    (by rw [seedIntersection_card,Nat.card_fin])).2
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := hs ⟨x,hx⟩
    exact ⟨i,congrArg (fun x : seedIntersection => (x : Model)) hi⟩
  · rintro ⟨i,rfl⟩
    exact seedCoordinate_mem_intersection i

/-- Native F membership at a literal kernel word is now an exact finite condition. -/
theorem nativeWord_mem_seedF_iff (m : Fin 8192) : nativeWord m ∈ seedF ↔
    ∃ i : Fin 128, seedCoordinate i = m := by
  constructor
  · intro hm
    obtain ⟨i,hi⟩ := (mem_seedIntersection_iff _).mp ⟨kernel_mem_sourceCore m,hm⟩
    exact ⟨i,kernelProduct_injective (Subtype.ext hi)⟩
  · rintro ⟨i,rfl⟩
    exact seedCoordinate_mem i

/-- The original max2 source subgroup preserves the same native point core. -/
theorem sourceCore_normalized (u : sourceSubgroup) :
    (u : Model) ∈ normalizer (sourceCore : Set Model) := by
  rw [sourceCore,← map_equiv_normalizer_eq,normalizer_firstCore]
  refine ⟨eH (sourceSubgroupEquivLocal u),?_,?_⟩
  · exact mem_centralizer_singleton_iff.mpr (eH_commute_z _).eq
  · simp only [eH_sourceSubgroupEquivLocal,MulAut.conj_apply,mul_assoc,
      mul_inv_cancel_left,mul_inv_cancel,mul_one,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe]

/-- An actual F occurrence obtained from an original max2 word. -/
@[expose] def wordF (w : List Bool) : Subgroup Model :=
  seedF.map (MulAut.conj ((actorWord w : Model)⁻¹)).toMonoidHom

/-- The ambient F conjugator for the word-defined occurrence. -/
theorem wordF_eq (w : List Bool) : wordF w = LinearFive.F.map
    (MulAut.conj ((actorWord w : Model)⁻¹ * BridgeCertificates.bridge⁻¹)).toMonoidHom := by
  rw [wordF,seedF,map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Transport the exact kernel intersection through the original max2 action. -/
theorem sourceCore_inf_wordF (w : List Bool) : sourceCore ⊓ wordF w =
    seedIntersection.map (MulAut.conj ((actorWord w : Model)⁻¹)).toMonoidHom := by
  have hn := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (sourceCore : Set Model)).inv_mem (sourceCore_normalized (actorWord w)))
  rw [seedIntersection,Subgroup.map_inf _ _ _ (MulAut.conj ((actorWord w : Model)⁻¹)).injective]
  simpa only [wordF,map_inv,MulEquiv.toMonoidHom_eq_coe] using congrArg (fun K : Subgroup Model => K ⊓ wordF w) hn.symm

/-- Exact finite membership for every actual word-defined F occurrence.
The same conjugator transports all 128 words, so the statement applies to
whole subgroups and can distinguish ambient F occurrences. -/
theorem nativeWord_mem_wordF_iff (w : List Bool) (m : Fin 8192) :
    nativeWord m ∈ wordF w ↔ ∃ i : Fin 128,
      (MulAut.conj ((actorWord w : Model)⁻¹)) (nativeWord (seedCoordinate i)) = nativeWord m := by
  constructor
  · intro hm
    have hh : nativeWord m ∈ sourceCore ⊓ wordF w := ⟨kernel_mem_sourceCore m,hm⟩
    rw [sourceCore_inf_wordF] at hh
    obtain ⟨x,hx,he⟩ := hh
    obtain ⟨i,rfl⟩ := (mem_seedIntersection_iff x).mp hx
    exact ⟨i,he⟩
  · rintro ⟨i,he⟩
    exact he ▸ mem_map_of_mem _ (seedCoordinate_mem i)

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
