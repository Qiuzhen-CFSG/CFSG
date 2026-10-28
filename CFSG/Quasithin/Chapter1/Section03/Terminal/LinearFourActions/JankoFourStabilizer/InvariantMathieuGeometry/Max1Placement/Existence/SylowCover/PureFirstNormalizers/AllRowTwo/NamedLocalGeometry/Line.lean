module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly.Elementary

/-!
# The literal line row and its full max4 normalizer

The shared row with index five is exactly the certified normal eight,
transported by the existing max4-to-max2 marking. The remaining five words
follow from the two checked multiplication tables; no new matrix certificate
or finite-row exhaustiveness assumption is needed. Its whole normalizer is
therefore the corresponding literal max4 conjugate.
Source: Kleidman--Wilson (1988), Corollary 1.2.2(a), pp.488--489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
open FiniteConfigurations SymmetricLinear
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
attribute [local irreducible] modelGroup matrixA matrixB

private def lineMask : Fin 8 → Fin 8192 := ![0,6607,1,3400,5254,6606,3401,5255]

private theorem line_step (i j k : Fin 8)
    (hij : NormalEight.productIndex i j = k)
    (hm : maskMultiply (lineMask i).val (lineMask j).val = (lineMask k).val)
    (hi : (MulAut.conj bridge) (NormalEight.element i : Model) = nativeWord (lineMask i))
    (hj : (MulAut.conj bridge) (NormalEight.element j : Model) = nativeWord (lineMask j)) :
    (MulAut.conj bridge) (NormalEight.element k : Model) = nativeWord (lineMask k) := by
  have he := congrArg (fun x : max4Subgroup => (x : Model)) (NormalEight.element_mul i j)
  rw [hij] at he
  rw [← he,Subgroup.coe_mul,map_mul,hi,hj]
  have hh := source_mask_multiply (lineMask i).val (lineMask j).val
  rw [hm] at hh
  exact (congrArg (fun x : sourceSubgroup => (x : Model)) hh).symm

private theorem line_element_coordinate (i : Fin 8) :
    (MulAut.conj bridge) (NormalEight.element i : Model) = nativeWord (lineMask i) := by
  have h1 : (MulAut.conj bridge) (NormalEight.element 1 : Model) = nativeWord (lineMask 1) := marking.1
  have h2 : (MulAut.conj bridge) (NormalEight.element 2 : Model) = nativeWord (lineMask 2) := by
    rw [marking.2.1]
    have hw : kernelProduct 1 = kernelFactor 0 := by
      change kernelFactor 0 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1)))))))))))) = _
      simp only [mul_one]
    change t = (kernelProduct 1 : Model)
    rw [hw]
    exact coe_sourceSeed_sq.symm
  have h3 : (MulAut.conj bridge) (NormalEight.element 3 : Model) = nativeWord (lineMask 3) := marking.2.2
  have h5 := line_step 1 2 5 rfl (by decide +kernel) h1 h2
  fin_cases i
  · change (MulAut.conj bridge) (NormalEight.element 0 : Model) = (kernelProduct 0 : Model)
    rw [NormalEight.element_zero,Subgroup.coe_one,map_one]
    simp [kernelProduct]
  · exact h1
  · exact h2
  · exact h3
  · exact line_step 1 3 4 rfl (by decide +kernel) h1 h3
  · exact h5
  · exact line_step 2 3 6 rfl (by decide +kernel) h2 h3
  · exact line_step 5 3 7 rfl (by decide +kernel) h5 h3

/-- The shared line row is the actual conjugate of the certified max4 eight. -/
theorem line_row_eq_eight : row 5 = max4Eight.map (MulAut.conj bridge).toMonoidHom := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨m,hm,rfl⟩
    have hex : ∃ i : Fin 8, lineMask i = m := by
      change m ∈ ({0,1,3400,3401,5254,5255,6606,6607} : Finset (Fin 8192)) at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨2,rfl⟩
      · exact ⟨3,rfl⟩
      · exact ⟨6,rfl⟩
      · exact ⟨4,rfl⟩
      · exact ⟨7,rfl⟩
      · exact ⟨5,rfl⟩
      · exact ⟨1,rfl⟩
    obtain ⟨i,rfl⟩ := hex
    exact ⟨NormalEight.element i,⟨NormalEight.element i,⟨i,rfl⟩,rfl⟩,line_element_coordinate i⟩
  · change (NormalEight.eight.map max4Subgroup.subtype).map (MulAut.conj bridge).toMonoidHom ≤ _
    rintro x ⟨y,⟨z,⟨i,rfl⟩,rfl⟩,rfl⟩
    change (MulAut.conj bridge) (NormalEight.element i : Model) ∈ row 5
    rw [line_element_coordinate]
    apply Subgroup.subset_closure
    refine ⟨lineMask i,?_,rfl⟩
    have h : ∀ i : Fin 8, lineMask i ∈ rowMasks 5 := by decide +kernel
    exact h i

/-- Whole-normalizer placement for row five, with no maximality or census premise. -/
theorem line_row_normalizer : normalizer (row 5 : Set Model) =
    max4Subgroup.map (MulAut.conj bridge).toMonoidHom := by
  rw [line_row_eq_eight,conjugate_eight_normalizer]

theorem line_row_nativeLocalPlacement :
    LargeCenterRadicals.NativeLocalPlacement (normalizer (row 5 : Set Model)) :=
  ⟨bridge,Or.inr (Or.inr (Or.inr line_row_normalizer))⟩

/-- The line row supplies the literal max4 restriction for an arbitrary radical
whose whole normalizer lies in this row normalizer. -/
theorem radical_local_of_line_row (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hPX : normalizer (P : Set Model) ≤ normalizer (row 5 : Set Model)) :
    let M := max4Subgroup.map (MulAut.conj bridge).toMonoidHom
    IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P :=
  radical_max4_of_eight_witness P (row 5) (row 5) bridge hP hPX le_rfl line_row_eq_eight

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
