module

public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.SpecificGroups.GL2.ThreeSolvable
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.GroupTheory.CComponent.TwoComponent.Involution
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# The involutory B₂ property for M₁₁ and M₂₃

Every involutory automorphism of M₁₁ has solvable fixed group GL₂(3).
For M₂₃, full innerness and exhaustive involution fusion identify the fixed
group with the marked centralizer. Its self-centralizing normal binary kernel
forces its odd core to be trivial. Thus its two-components are quasisimple;
no ordinary-component premise is used.

Sources: GLS II, Definition 2.4; GLS III, Tables 5.3a and 5.3d.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu

/-- The complete involutory B₂ condition on the Witt-design M₁₁. -/
theorem m11_hasInvolutoryB2 : HasInvolutoryB2 M11 := by
  apply HasInvolutoryB2.of_fixed_solvable
  intro a ha
  let := Matrix.GeneralLinearGroup.three_isSolvable
  let e := m11InvolutoryAutFixedEquiv a ha
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The actual fixed subgroup of every involutory M₂₃ automorphism has trivial odd core. -/
theorem m23_involution_fixed_oddCore_eq_bot (a : MulAut M23) (ha : orderOf a = 2) :
    pPrimeCore 2 a.fixedSubgroup = ⊥ := by
  obtain ⟨e⟩ := M23Geometry.InvolutionCentralizer.fixedSubgroup_equiv_representative_of_inner
    a ha (m23_involution_automorphism_inner a ha)
  apply pPrimeCore_eq_bot_of_equiv e
  apply pPrimeCore_eq_bot_of_centralizer_pCore_le 2
  have hle : M23Geometry.InvolutionCentralizer.kernel ≤
      pCore 2 M23Geometry.InvolutionCentralizer.representativeCentralizer :=
    le_sSup ⟨inferInstance, M23Geometry.InvolutionCentralizer.kernel_isTwoGroup⟩
  exact (centralizer_le hle).trans
    (M23Geometry.InvolutionCentralizer.kernel_selfCentralizing.trans hle)

/-- The complete involutory B₂ condition on the Witt-design M₂₃. -/
theorem m23_hasInvolutoryB2 : HasInvolutoryB2 M23 :=
  HasInvolutoryB2.of_fixed_oddCore_eq_bot m23_involution_fixed_oddCore_eq_bot

end Sporadic.Mathieu
