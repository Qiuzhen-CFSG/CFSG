module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.RowIncidence

/-!
# Second-class members in every nonline canonical F intersection

The exact occurrence table supplies a common native word for each nonline row.
The original native conjugacy forest identifies it as second-class. Thus the
canonical intersection is mixed, elementary and contained in a conjugate of F;
the proved nonfirst F endpoint controls its whole normalizer. Maximal two-locality
then supplies the literal named-local equality for the original row normalizer.
The arbitrary-radical application retains the actual subgroup restriction maps.
Source: Kleidman--Wilson (1988), Section 2.1 and Proposition 2.2.3, pp.488--491.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
open ElementaryNormalizerCover FiniteConfigurations RowIncidence OccurrenceTable
open Cardinality.LocalInvolutionCensus Cardinality.LocalInvolutionCensus.Coordinates
open Cardinality.LocalInvolutionCensus.FiberCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
attribute [local irreducible] modelGroup matrixA matrixB
attribute [local instance 2000] Finset.decidableDforallFinset
set_option Elab.async false

private theorem mixed_positive : ∀ i : Fin 26, i ≠ 5 → ∀ j ∈ containing i,
    combo j (preimage j (mixedWitness i)) = mixedWitness i := by decide +kernel

private theorem mixed_class : ∀ i : Fin 26, i ≠ 5 → mixedWitness i ∈ masks 3 := by
  decide +kernel

/-- A literal common second-class element belongs to every ambient occurrence. -/
theorem mixedWitness_mem_fIntersection (i : Fin 26) (hi : i ≠ 5) :
    nativeWord (mixedWitness i) ∈ fIntersection (row i) := by
  apply (mem_row_fIntersection_iff i _).mpr
  intro j hj
  rw [← mixed_positive i hi j hj]
  exact combo_mem j _

/-- The witness is second-class by the already certified native conjugacy forest. -/
theorem mixedWitness_second (i : Fin 26) (hi : i ≠ 5) :
    IsConj Cardinality.LocalInvolutionCensus.t (nativeWord (mixedWitness i)) := by
  have hc := Forest.listed_isConj_of_edges (Forest.edges Cardinality.Thompson.max2_card.le)
    3 (mixedWitness i) (mixed_class i hi)
  have he : sourceElement (fiberIndex 3) (mixedWitness i) = kernelProduct (mixedWitness i) := by
    change kernelProduct (mixedWitness i) * 1 = kernelProduct (mixedWitness i)
    exact mul_one _
  rw [he] at hc
  have hl := eH.map_isConj (sourceSubgroupEquivLocal.toMonoidHom.map_isConj hc)
  simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,sourceEquiv_representative] at hl
  have ht : IsConj Cardinality.LocalInvolutionCensus.t (eH (representative 3)) :=
    firstTarget_isConj_representative 3
  apply (ht.trans hl).trans
  apply isConj_iff.mpr
  refine ⟨h,?_⟩
  rw [eH_sourceSubgroupEquivLocal]
  simp [nativeWord,mul_assoc]

theorem mixedWitness_not_first (i : Fin 26) (hi : i ≠ 5) :
    ¬ IsConj a (nativeWord (mixedWitness i)) := by
  intro hc
  apply not_isConj_z_t
  simpa only [z_eq_a] using hc.trans (mixedWitness_second i hi).symm

theorem mixedWitness_order (i : Fin 26) (hi : i ≠ 5) :
    orderOf (nativeWord (mixedWitness i)) = 2 := by
  obtain ⟨g,hg⟩ := nonline_row_le_F_conjugate i hi
  let := fIntersection_elementary (row i) g hg
  apply orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (mixedWitness_mem_fIntersection i hi))
  intro he
  have hc : ∀ i : Fin 26, i ≠ 5 → mixedWitness i ≠ 0 := by decide +kernel
  exact hc i hi (nativeWord_injective (he.trans nativeWord_zero.symm))

/-- Every shared nonline row has the required whole-normalizer placement;
no occurrence, mixedness or normalizer-containment premise remains. -/
theorem nonline_row_whole_normalizer (i : Fin 26) (hi : i ≠ 5)
    (hmax : IsMaximalTwoLocal (normalizer (row i : Set Model))) :
    LargeCenterRadicals.NativeLocalPlacement (normalizer (row i : Set Model)) :=
  nonline_row_nativeLocalPlacement i hi hmax (nativeWord (mixedWitness i))
    (mixedWitness_mem_fIntersection i hi) (mixedWitness_order i hi) (mixedWitness_not_first i hi)

/-- The literal arbitrary-radical restriction for every nonline row. -/
theorem radical_local_of_nonline_row_unconditional (P : Subgroup Model) (hP : P.IsPRadical 2)
    (i : Fin 26) (hi : i ≠ 5)
    (hPX : normalizer (P : Set Model) ≤ normalizer (row i : Set Model)) :
    ∃ (k : Model) (H : Subgroup Model), IsTwoLocal H ∧
      (H = LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
        H = max1.map (MulAut.conj k).toMonoidHom) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P :=
  radical_local_of_nonline_row P hP i hi hPX (nativeWord (mixedWitness i))
    (mixedWitness_mem_fIntersection i hi) (mixedWitness_order i hi) (mixedWitness_not_first i hi)

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
