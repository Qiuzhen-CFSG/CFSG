module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.Lattice
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.Signs

/-!
# Transporting the integral action through a genuine lattice comparison

A rational linear isometry taking the displayed integral lattice onto the
retained Leech lattice gives an actual integral Leech action. Faithfulness
survives conjugation and restriction. The rational action detects minus
identity, so its central-sign preimage is exactly `matrixSigns`.

All comparison hypotheses remain explicit: this does not assert the final
unconditional `matrixToLeech`. `MarkedComparison` applies the construction
through the existing attributed ATLAS icosian-to-Leech equivalence.
Source conventions: John Bray's ATLAS matrices and Gerald Höhn's retained
Leech integral/rational isometry equivalence.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Conway Atlas.LinearAlgebra
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

variable (e : Space ≃ₗ[ℚ] RationalCoordinates)
  (heForm : ∀ x y, rationalForm (e x) (e y) = form x y)
  (heLattice : ∀ x, x ∈ lattice ↔ e x ∈ rationalLeech)

def comparedAction : matrixGroup →* (RationalCoordinates ≃ₗ[ℚ] RationalCoordinates) :=
  (linearAutomorphismCongr e).toMonoidHom.comp linearAction

include heForm heLattice in
theorem comparedAction_isometry (g : matrixGroup) :
    comparedAction e g ∈ rationalLatticeIsometries := by
  constructor
  · intro x y
    change rationalForm (e (linearAction g (e.symm x))) (e (linearAction g (e.symm y))) = _
    rw [heForm, linearAction_form]
    simpa only [LinearEquiv.apply_symm_apply] using (heForm (e.symm x) (e.symm y)).symm
  · intro x
    change x ∈ rationalLeech ↔ e (linearAction g (e.symm x)) ∈ rationalLeech
    rw [← heLattice, ← linearAction_lattice]
    simpa only [LinearEquiv.apply_symm_apply] using (heLattice (e.symm x)).symm

def comparedLatticeAction : matrixGroup →* rationalLatticeIsometries :=
  (comparedAction e).codRestrict rationalLatticeIsometries
    (comparedAction_isometry e heForm heLattice)

/-- A genuine rational lattice comparison gives integral Leech isometries.
The comparison itself is not asserted here. -/
def toLeechOfComparison : matrixGroup →* LeechIsometryGroup :=
  fullIsometryEquiv.symm.toMonoidHom.comp (comparedLatticeAction e heForm heLattice)

theorem toLeechOfComparison_injective :
    Function.Injective (toLeechOfComparison e heForm heLattice) := by
  intro g h he
  apply linearAction_injective
  apply (linearAutomorphismCongr e).injective
  have hr := congrArg (fun u : LeechIsometryGroup => (fullIsometryEquiv u).val) he
  simpa only [toLeechOfComparison, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, comparedLatticeAction, MonoidHom.codRestrict_apply,
    comparedAction] using hr

/-- The exact rational extension retains the concrete generator action. -/
theorem toLeechOfComparison_extension (g : matrixGroup) :
    (fullIsometryEquiv (toLeechOfComparison e heForm heLattice g)).val =
      comparedAction e g := by
  exact congrArg Subtype.val (fullIsometryEquiv.apply_symm_apply _)

private theorem fullIsometryEquiv_negation :
    (fullIsometryEquiv negationIsometry).val = LinearEquiv.neg ℚ := by
  apply LinearEquiv.toLinearMap_injective
  symm
  exact rationalExtension_unique negationIsometry.val
    (-LinearMap.id : RationalCoordinates →ₗ[ℚ] RationalCoordinates) (by
      intro x
      rw [negationIsometry_apply]
      simp)

private theorem conjugate_neg :
    linearAutomorphismCongr e (LinearEquiv.neg ℚ) = LinearEquiv.neg ℚ := by
  ext x
  simp

theorem toLeechOfComparison_eq_negation (g : matrixGroup) :
    toLeechOfComparison e heForm heLattice g = negationIsometry ↔ g.val = -1 := by
  rw [← linearAction_eq_neg_iff]
  constructor
  · intro h
    apply (linearAutomorphismCongr e).injective
    rw [conjugate_neg]
    change comparedAction e g = _
    rw [← toLeechOfComparison_extension e heForm heLattice, h, fullIsometryEquiv_negation]
  · intro h
    apply fullIsometryEquiv.injective
    apply Subtype.ext
    rw [toLeechOfComparison_extension, fullIsometryEquiv_negation]
    change linearAutomorphismCongr e (linearAction g) = _
    rw [h, conjugate_neg]

/-- Comparison preserves exactly the two central signs, with no splitting assumption. -/
theorem toLeechOfComparison_signs :
    leechCentralSigns.comap (toLeechOfComparison e heForm heLattice) = matrixSigns := by
  ext g
  change toLeechOfComparison e heForm heLattice g ∈ leechCentralSigns ↔ _
  rw [leechCentralSigns_mem, mem_matrixSigns,
    toLeechOfComparison_eq_negation, map_eq_one_iff _
      (toLeechOfComparison_injective e heForm heLattice)]
  simp only [Subtype.ext_iff, OneMemClass.coe_one]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
