module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Marking.Conjugator
public import Theory.AtlasPort.Janko2.Conway.IcosianScalarIsometries

/-!
# Conjugating the icosian unit i to the marked Leech lift

Inverse right multiplication by i permutes the four quaternion coordinates
with signs. The finite coefficient identity below transports this action
through the existing icosian comparison matrix. A second finite identity
checks that the signed Golay permutation from `Marking.Conjugator` intertwines
this action with the exact signed permutation `markedLift`.

The rational comparison is an integral lattice equivalence, so these coordinate
identities prove conjugacy inside the actual Leech isometry group, and hence
inside its central quotient. `Short.Marking` uses this conjugacy to mark the
specified scalar double transposition via the actual scalar A₅ embedding.

Source context: Aschbacher, *Sporadic Groups* (1994), root-four definitions
p.269, Lemma 46.9 p.254, and Lemma 49.5 pp.283–284. The quaternion action and
comparison matrix are the attributed ATLAS ports; no converse to the
order-four lift statement is assumed.
-/

@[expose] public section

open Atlas.Codes Atlas.Algebra Atlas.Lattices Atlas.Conway
open Atlas.G2.ConwayRootFour
open scoped BigOperators Matrix
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Marking

set_option backward.isDefEq.respectTransparency false

/-- The actual norm-one integral quaternion i. -/
def unitI : icosianNormOneGroup := icosianNormOneGroupOf icosianI icosianI_mem (by
  rw [icosianNorm_coordinates]
  norm_num [icosianI])

private theorem scalar_unitI_apply (z : IcosianRationalCoordinates) :
    icosianScalarRepresentation unitI z = fun i => z i * (-icosianI) := by
  funext i
  change z i * star icosianI = _
  congr 1
  ext <;> simp [icosianI]

def realSwitch : Equiv.Perm (Fin 4) where
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv := by decide
  right_inv := by decide

def realPerm : Equiv.Perm IcosianRealIndex :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr realSwitch (Equiv.refl _))

def realSign (q : IcosianRealIndex) : ℚ := ![1,-1,-1,1] q.2.1

def scalarPerm (p : Omega) : Omega := coordinateIndex.symm
  (![1,0,5,4,3,2,7,6,14,15,11,10,13,12,8,9,22,23,19,18,21,20,16,17]
    (coordinateIndex p))

def scalarSign (p : Omega) : ℚ :=
  ![-1,1,1,-1,1,-1,-1,1,-1,1,-1,1,1,-1,1,-1,-1,1,1,-1,-1,1,1,-1]
    (coordinateIndex p)

private theorem scalar_real_apply (z : IcosianRationalCoordinates) (q : IcosianRealIndex) :
    icosianRealCoordinates (icosianScalarRepresentation unitI z) q =
      realSign q * icosianRealCoordinates z (realPerm q) := by
  rw [scalar_unitI_apply]
  rcases q with ⟨i,j,k⟩
  fin_cases j <;> fin_cases k <;>
    simp [icosianRealCoordinates, icosianQuaternionCoordinate, icosianI,
      realPerm, realSwitch, realSign]

private theorem comparison_coefficients (p : Omega) (q : IcosianRealIndex) :
    icosianComparisonMatrix p q * realSign q =
      scalarSign p * icosianComparisonMatrix (scalarPerm p) (realPerm q) := by
  revert p q
  decide +kernel

private theorem scalar_comparison_apply (z : IcosianRationalCoordinates) (p : Omega) :
    icosianComparison (icosianScalarRepresentation unitI z) p =
      scalarSign p * icosianComparison z (scalarPerm p) := by
  simp only [icosianComparison_apply, Matrix.mulVec, dotProduct, scalar_real_apply]
  simp_rw [← mul_assoc, comparison_coefficients, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp realPerm
    (fun q => icosianComparisonMatrix (scalarPerm p) q * icosianRealCoordinates z q)

def bitSign (b : Bit) : ℚ := if b = 0 then 1 else -1

private theorem conjugator_coefficients (p : Omega) :
    scalarPerm (markingPerm.symm p) = markingPerm.symm (coordinateSwap.val.symm p) ∧
    bitSign (markingSign.val p) * scalarSign (markingPerm.symm p) =
      bitSign (signWord.val p) * bitSign (markingSign.val (coordinateSwap.val.symm p)) := by
  revert p
  decide +kernel

private theorem comparison_intertwining (z : IcosianRationalCoordinates) (p : Omega) :
    bitSign (markingSign.val p) *
      icosianComparison (icosianScalarRepresentation unitI z) (markingPerm.symm p) =
    bitSign (signWord.val p) *
      (bitSign (markingSign.val (coordinateSwap.val.symm p)) *
        icosianComparison z (markingPerm.symm (coordinateSwap.val.symm p))) := by
  rw [scalar_comparison_apply, ← mul_assoc, (conjugator_coefficients p).2,
    (conjugator_coefficients p).1, mul_assoc]

private theorem conjugator_rational_apply (x : leech) (p : Omega) :
    rationalEmbedding (markingConjugator.val x).val p =
      bitSign (markingSign.val p) * rationalEmbedding x.val (markingPerm.symm p) := by
  change ((if markingSign.val p = 0 then x.val (markingPerm.symm p)
    else -x.val (markingPerm.symm p) : ℤ) : ℚ) = _
  simp only [bitSign]
  split_ifs <;> simp [rationalEmbedding]

private theorem marked_rational_apply (x : leech) (p : Omega) :
    rationalEmbedding (markedLift.val x).val p =
      bitSign (signWord.val p) * rationalEmbedding x.val (coordinateSwap.val.symm p) := by
  change (((markedLift.val x).val p : ℤ) : ℚ) = _
  rw [markedLift_apply]
  simp only [bitSign]
  split_ifs <;> simp [rationalEmbedding]

private theorem scalar_rational_apply (x : leech) :
    rationalEmbedding ((icosianScalarsToCo0 unitI).val x).val =
      icosianComparison (icosianScalarRepresentation unitI
        (icosianComparison.symm (rationalEmbedding x.val))) := by
  have h := congrArg (fun g : rationalLatticeIsometries => g.val (rationalEmbedding x.val))
    (icosianScalarsToCo0_extension unitI)
  change rationalExtension (icosianScalarsToCo0 unitI).val (rationalEmbedding x.val) = _ at h
  rw [rationalExtension_agrees] at h
  exact h

/-- An equality of actual integral Leech isometries, before taking the quotient. -/
theorem markingConjugator_intertwines :
    markingConjugator * icosianScalarsToCo0 unitI = markedLift * markingConjugator := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  apply rationalEmbedding_injective
  ext p
  change rationalEmbedding (markingConjugator.val ((icosianScalarsToCo0 unitI).val x)).val p =
    rationalEmbedding (markedLift.val (markingConjugator.val x)).val p
  simp only [conjugator_rational_apply, marked_rational_apply, scalar_rational_apply]
  simpa only [LinearEquiv.apply_symm_apply] using
    comparison_intertwining (icosianComparison.symm (rationalEmbedding x.val)) p

/-- The concrete conjugator proves conjugacy already in Co₀. -/
theorem scalarI_isConj_markedLift : IsConj (icosianScalarsToCo0 unitI) markedLift := by
  apply isConj_iff.mpr
  refine ⟨markingConjugator, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact markingConjugator_intertwines

/-- Project the checked conjugacy through the literal central-sign quotient. -/
theorem scalarI_projection_isConj_marked :
    IsConj (leechCentralProjection (icosianScalarsToCo0 unitI)) markedInvolution :=
  leechCentralProjection.map_isConj scalarI_isConj_markedLift


end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Marking
