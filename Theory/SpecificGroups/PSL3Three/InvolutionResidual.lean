module

public import Theory.SpecificGroups.GL2.InvolutionLocalResidual
public import Theory.SpecificGroups.PSL3Three.InnerInvolutionCentralizer

/-!
# The involution-centralizer residual in PSL₃(3)

The canonical SL₃(3)-to-PSL₃(3) equivalence identifies every involution
centralizer with the actual GL₂(3) block group. The shared residual calculation
retains the original involution and the literal centralizer restriction map.
Source: Aschbacher--Smith, Lemma 2.5.15, printed pp.558--559.
-/

public section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Three

/-- The full centralizer of the specified involution is GL₂(3). -/
noncomputable def involutionCentralizerEquivGL (z : PSL) (hz : orderOf z = 2) :
    centralizer ({z} : Set PSL) ≃* GL (Fin 2) (ZMod 3) :=
  (CentralizerSmallKernelTransport.centralizerEquiv equiv.symm z).trans
    (Matrix.SL3.involutionCentralizerEquiv (ZMod 3) (equiv.symm z)
      ((equiv.symm.orderOf_eq z).trans hz) (by decide))

/-- The three actual local facts used in 2.5.15, with no model premise. -/
theorem involution_residual_structure (z : PSL) (hz : orderOf z = 2) :
    Nonempty (GLTwoThreeLocal.residual z ≃* SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
    centralizer (GLTwoThreeLocal.residual z : Set PSL) = zpowers z ∧
    Function.Surjective (GLTwoThreeLocal.action z) := by
  let e := involutionCentralizerEquivGL z hz
  exact ⟨⟨GLTwoThreeLocal.residualEquivSL z e⟩,
    GLTwoThreeLocal.centralizer_residual z e hz, GLTwoThreeLocal.action_surjective z e⟩

end Matrix.PSL3Three
