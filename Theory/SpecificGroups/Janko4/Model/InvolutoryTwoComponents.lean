module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.Reduction
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.CComponent.TwoComponent.Involution
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# The involutory B₂ property for the actual J₄ matrix model

Both full marked centralizers contain self-centralizing normal two-subgroups,
so their odd cores vanish. The checked max1 fusion, promoted by its odd index,
covers every element involution. Full abstract automorphism innerness then
covers every involutory automorphism. Simplicity may be inherited from an actual
isomorphism to the model; its full-center alternative is handled by solvability.

The seed-to-word marking below is the same genuine conjugacy used in the
Chapter 16 marked-centralizer assembly. No equality of those distinct elements
or classification of ordinary components substitutes for the two-component claim.

Sources: GLS II, Definition 2.4; GLS III, Table 5.3i.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4
open InvolutionCentralizers

attribute [local irreducible] modelGroup matrixA matrixB

private theorem first_oddCore_eq_bot : pPrimeCore 2 First.centralizer = ⊥ := by
  exact @pPrimeCore_eq_bot_of_equiv First.centralizer
    OuterReduction.FixedGenerator.NormalizerSquares.involutionCentralizer
    inferInstance inferInstance 2 First.centralizerEquiv
    (pPrimeCore_eq_bot_of_centralizer_pCore_le 2
      OuterReduction.FixedGenerator.NormalizerSquares.localTwoCoreCentralizerControl.1)

private theorem second_oddCore_eq_bot : pPrimeCore 2 Second.ambientCentralizer = ⊥ := by
  apply pPrimeCore_eq_bot_of_centralizer_pCore_le 2
  let := Second.ambientKernel_elementary
  have hp : IsPGroup 2 Second.ambientKernel := IsElementaryAbelian.isPGroup 2 _
  have hle : Second.ambientKernel ≤ pCore 2 Second.ambientCentralizer :=
    le_sSup ⟨inferInstance, hp⟩
  exact (centralizer_le hle).trans (Second.ambientKernel_selfCentralizing.le.trans hle)

private theorem seed_isConj_second : IsConj (Second.seed : Model) ((a * b * a * b * b) ^ 5) := by
  obtain ⟨g, hg⟩ := Simplicity.Max1Fusion.seed_fuses_second matrixA_mul_self matrixB_pow_four
  have ha : Simplicity.a matrixA_mul_self = a := by apply toMatrix_injective; rfl
  have hb : Simplicity.b matrixB_pow_four = b := by apply toMatrix_injective; rfl
  rw [ha, hb] at hg
  have hw : Simplicity.word a b "ababb" = a * b * a * b * b := by
    simp [Simplicity.word, mul_assoc]
  rw [hw] at hg
  exact isConj_iff.mpr ⟨g, hg.symm⟩

private theorem fixed_oddCore_of_isConj {x y : Model} (h : IsConj x y)
    (hx : pPrimeCore 2 (centralizer ({x} : Set Model)) = ⊥) :
    pPrimeCore 2 (MulAut.conj y).fixedSubgroup = ⊥ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he : MulAut.congr (MulAut.conj g) (MulAut.conj x) = MulAut.conj y := by
    rw [MulAut.congr_conj]
    exact congrArg MulAut.conj hg
  let e := MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj x)
  rw [he] at e
  exact pPrimeCore_eq_bot_of_equiv
    (e.symm.trans (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj x))) hx

/-- Both element-involution classes have trivial odd core in their full centralizers. -/
theorem inner_involution_fixed_oddCore_eq_bot (x : Model) (hx : orderOf x = 2) :
    pPrimeCore 2 (MulAut.conj x).fixedSubgroup = ⊥ := by
  rcases OuterReduction.involution_isConj_of_max1_odd_index
    OuterReduction.max1_odd_index_unconditional hx with h | h
  · exact fixed_oddCore_of_isConj h first_oddCore_eq_bot
  · exact fixed_oddCore_of_isConj (seed_isConj_second.trans h) second_oddCore_eq_bot

/-- All involutory automorphisms satisfy B₂, under inherited model simplicity. -/
theorem hasInvolutoryB2 [IsSimpleGroup Model] : HasInvolutoryB2 Model := by
  rcases (inferInstance : (center Model).Normal).eq_bot_or_eq_top with hc | hc
  · apply HasInvolutoryB2.of_fixed_oddCore_eq_bot
    intro r hr
    obtain ⟨x, hx, rfl, _⟩ := MulAut.inner_involution_representative hc r hr
      (AdequateLocal.exists_eq_conj r)
    exact inner_involution_fixed_oddCore_eq_bot x hx
  · exact (HasInvolutoryB2.of_solvable (G := center Model)).of_mulEquiv
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hc.symm))

end Janko4
