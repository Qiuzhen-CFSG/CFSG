module

public import Theory.GroupTheory.SolvableResidual.DerivedCentralCover
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Inner.Conjugacy

/-!
# Perfect residuals of central two-extensions of G₂(2)

The literal derived group of the binary octonion automorphism group is
identified with a field-nine projective unitary matrix group. The proved
odd-parameter PSU₃ two-kernel exclusion then makes the residual restriction
of any central two-extension an isomorphism. Its evaluation formula keeps
the original map. Involution conjugacy transports through the same actual
comparison; no group-family tag replaces a matrix isomorphism.

Only the derived comparison, involution fusion and two-primary multiplier
bound are used. Sources: Aschbacher--Smith 14.3.22, printed p.999, and the
residual-cover correction in `docs/quasithin-proof-basis.md`; I.1.3(2) and
I.1.4(2), printed pp.407--408. Attribution for the octonion carrier is in
`Theory.SpecificGroups.SU3.BinaryG2Comparison` and `LICENSES/ATLAS.txt`.
-/

@[expose] public section

open Subgroup PerfectCentralCovering BenderSuzuki.MatrixGroups
namespace Atlas.G2.BinaryResidualCover
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

/-- The concrete ternary identity Hermitian form over the nine-element field. -/
noncomputable def unitaryForm : HermitianForm 3 FiniteField.Nine :=
  identityForm starRingAut star_involutive

/-- An actual projective-matrix equivalence with the literal derived octonion group. -/
noncomputable def unitaryEquiv : ProjectiveSpecialUnitaryMatrixGroup unitaryForm ≃*
    commutator (Model (ZMod 2)) :=
  unitaryForm.projectiveEquivBinaryG2Derived FiniteField.Nine.natCard
    FiniteField.Nine.star_eq_cube

private instance derived_perfect : Group.IsPerfect (commutator (Model (ZMod 2))) := by
  rw [BinaryParabolicPair.commutator_eq_longRootClosure]
  exact BinaryException.H_isPerfect

/-- The actual derived subgroup of G₂(2) has index two. -/
theorem derived_index : (commutator (Model (ZMod 2))).index = 2 := by
  rw [BinaryParabolicPair.commutator_eq_longRootClosure, BinaryException.index_H]

/-- The derived octonion group has a single class of involutions. -/
theorem derived_involutions_isConj (a b : commutator (Model (ZMod 2)))
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  have h := HermitianForm.InvolutionConjugateBounds.Inner.projective_involutions_isConj
    unitaryForm (by decide : Nat.Prime 3) (by decide : 3 ≠ 2)
    FiniteField.Nine.natCard FiniteField.Nine.star_eq_cube
    (unitaryEquiv.symm a) (unitaryEquiv.symm b)
    ((unitaryEquiv.symm.orderOf_eq a).trans ha) ((unitaryEquiv.symm.orderOf_eq b).trans hb)
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.apply_symm_apply] using unitaryEquiv.toMonoidHom.map_isConj h

variable {E : Type*} [Group E] [Finite E]

/-- The literal residual restriction has trivial central two-kernel. -/
theorem residualMap_bijective (f : E →* Model (ZMod 2)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2) :
    Function.Bijective (residualDerivedMap f) := by
  let d := residualDerivedCover f hf hc
  let c : Cover (solvableResidual E) (ProjectiveSpecialUnitaryMatrixGroup unitaryForm) := {
    toMonoidHom := unitaryEquiv.symm.toMonoidHom.comp d.toMonoidHom
    surjective := unitaryEquiv.symm.surjective.comp d.surjective
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ unitaryEquiv.symm.injective]
      exact d.ker_le_center }
  have hodd := HermitianForm.UniversalCover.OddKernelBound.TwoPrimary.not_two_dvd_kernel_of_odd_prime_power
    unitaryForm (p := 3) (e := 1) (by decide) (by decide) (by decide)
    (by simpa only [pow_one] using
      (show Nat.card FiniteField.Nine = 3 ^ 2 from FiniteField.Nine.natCard))
    (by intro x; simpa only [pow_one] using
      (show unitaryForm.conj x = x ^ 3 from FiniteField.Nine.star_eq_cube x)) c
  have hk' : c.toMonoidHom.ker = (residualDerivedMap f).ker :=
    MonoidHom.ker_comp_of_injective _ _ unitaryEquiv.symm.injective
  rw [hk'] at hodd
  exact residualDerivedMap_bijective_of_two_kernel f hf hk hodd

/-- The residual isomorphism induced by the original extension map. -/
noncomputable def residualEquiv (f : E →* Model (ZMod 2)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2) :
    solvableResidual E ≃* commutator (Model (ZMod 2)) :=
  MulEquiv.ofBijective (residualDerivedMap f) (residualMap_bijective f hf hc hk)

/-- The residual isomorphism is the restriction of f. -/
theorem residualEquiv_apply (f : E →* Model (ZMod 2)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2) (x : solvableResidual E) :
    (residualEquiv f hf hc hk x : Model (ZMod 2)) = f x := rfl

/-- The commutator premise in the source puts its marked involution in the residual. -/
theorem commutator_eq_residual (f : E →* Model (ZMod 2)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2) :
    commutator E = solvableResidual E :=
  commutator_eq_residual_of_two_kernel f hf hk derived_index (residualMap_bijective f hf hc hk)

/-- The central-kernel-residual product has index two. -/
theorem residual_join_index (f : E →* Model (ZMod 2)) (hf : Function.Surjective f) :
    (f.ker ⊔ solvableResidual E).index = 2 :=
  residual_join_kernel_index f hf derived_index

/-- The original residual has one involution class. -/
theorem residual_involutions_isConj (f : E →* Model (ZMod 2)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2)
    (a b : solvableResidual E) (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  let e := residualEquiv f hf hc hk
  have h := derived_involutions_isConj (e a) (e b)
    ((e.orderOf_eq a).trans ha) ((e.orderOf_eq b).trans hb)
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.symm_apply_apply] using e.symm.toMonoidHom.map_isConj h
end Atlas.G2.BinaryResidualCover
