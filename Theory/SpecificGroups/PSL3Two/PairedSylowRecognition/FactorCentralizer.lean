module

public import Theory.GroupTheory.PairedInvolutiveExtension.FactorCentralizers
public import Theory.SpecificGroups.PSL3Two.PairedSylowRecognition
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.SylowModels

/-!
# The first-factor centralizer in the standard paired Sylow subgroup

The literal second-coordinate map identifies this centralizer with the
binary Borel subgroup. The established dihedral recognition of every
PSL₃(2) Sylow two-subgroup therefore gives an explicit D₈ model. The inverse
coordinate map is d ↦ (1,d), so the original factor and Sylow markings
are preserved up to the stated dihedral equivalence.

Source: the core embedding in Aschbacher--Smith, proof of 2.4.34,
printed p.548 of the 1 March 2004 manuscript.
-/

@[expose] public section
namespace Matrix.PSL3Two.PairedSylowRecognition
open Subgroup Theory.GroupTheory.PairedInvolutiveExtension MarkedAutomorphisms
abbrev firstFactorCentralizer : Subgroup StandardModel :=
  centralizer (Set.range (fun c : SL => base diagram diagram_involutive c 1)) ⊓ standardPaired
/-- The actual centralizer is the second Borel factor. -/
noncomputable def firstFactorCentralizerEquivBorel : firstFactorCentralizer ≃* borelSL := by
  letI : Nontrivial SL :=
    ⟨⟨PairedGraphInputs.highestRoot, 1, PairedGraphInputs.highestRoot_ne_one⟩⟩
  exact firstFactorCentralizerEquiv diagram diagram_involutive center_eq_bot diagram_ne_conj
    borelSL diagram_stable_borel

theorem card_firstFactorCentralizer : Nat.card firstFactorCentralizer = 8 :=
  (Nat.card_congr firstFactorCentralizerEquivBorel.toEquiv).trans card_borelSL

def borelSylow : Sylow 2 SL := Sylow.ofCard borelSL (by
  rw [card_borelSL, card_SL]
  decide +kernel)
/-- The binary Borel has the established dihedral Sylow model. -/
noncomputable def borelEquivDihedral : borelSL ≃* DihedralGroup 4 := by
  let P := borelSylow.mapSurjective (f := equiv.toMonoidHom) equiv.surjective
  let eP : borelSL ≃* P := borelSL.equivMapOfInjective equiv.toMonoidHom equiv.injective
  exact eP.trans (Classical.choice (Matrix.PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral P))
/-- Dihedral recognition on the literal first-factor centralizer. -/
noncomputable def firstFactorCentralizerEquivDihedral : firstFactorCentralizer ≃* DihedralGroup 4 :=
  firstFactorCentralizerEquivBorel.trans borelEquivDihedral
@[simp] theorem firstFactorCentralizerEquivBorel_apply (x : firstFactorCentralizer) :
    (firstFactorCentralizerEquivBorel x : SL) = x.val.left.2 := rfl
@[simp] theorem firstFactorCentralizerEquivBorel_symm_apply (d : borelSL) :
    (firstFactorCentralizerEquivBorel.symm d : StandardModel) = base diagram diagram_involutive 1 d := rfl
end Matrix.PSL3Two.PairedSylowRecognition
