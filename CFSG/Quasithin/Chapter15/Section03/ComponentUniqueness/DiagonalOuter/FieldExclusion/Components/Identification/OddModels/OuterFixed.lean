module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.OddModels.Reduction
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph.Equivalence
public import Theory.SpecificGroups.SU3.TernaryOrthogonalThreeRank.Components
public import Theory.SpecificGroups.SU3.OddInvolutionFixed
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Odd-prime parameters from outer-involution components

For both actual PSL₃(p) and PSU₃(p), an outer involution fixes a ternary
special orthogonal group over the field of order p. The shared orthogonal
component calculation identifies any component with the adjoint PSL₂(p)
image, so an actual PSL₃(2) component forces p = 7.

The linear branch uses surjectivity of the fixed-point isometry map, keeping
componenthood relative to the full fixed group. The unitary branch derives
the original conjugation's fixed-field order from the supplied Frobenius
formula and keeps arbitrary nondegenerate Hermitian forms. No fixed-group
classification or parameter sieve is an additional premise. The odd-model
assembly separately excludes PSU₃(7) using its supplied rank-two hypothesis.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, proof of 15.3.38,
printed p.1137, and Theorem C, printed p.33; GLS3, §§2.7 and 4.3.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

/-- An outer involution with a PSL₃(2) component in its whole fixed group
forces the prime-field PSL₃ parameter to be seven. -/
theorem linear_outer_component_prime_eq_seven
    {F : Type*} [Field F] [Finite F]
    [IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)]
    (hns : ¬ Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (a : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
    (ha : orderOf a = 2) (hout : ¬ ∃ k, a = MulAut.conj k)
    {D : Subgroup a.fixedSubgroup} (hD : IsComponent a.fixedSubgroup D)
    (e : D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) : p = 7 := by
  obtain ⟨J, hJ, ⟨f⟩⟩ := Matrix.PSL3.OddInvolutionFixed.outer_fixed_equiv_orthogonal
    hns hp ho hF a (ha ▸ pow_orderOf_eq_one a) hout
  exact prime_eq_seven_of_orthogonal_component J hJ hp ho hF (hD.map_equiv f)
    ((D.equivMapOfInjective f.toMonoidHom f.injective).symm.trans e)

/-- The same parameter calculation for every nondegenerate unitary form.
The field has order p², while the original Frobenius involution fixes p elements. -/
theorem unitary_outer_component_prime_eq_seven
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hE : Nat.card E = p ^ 2)
    (hconj : ∀ x, J.conj x = x ^ p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : orderOf a = 2) (hout : ¬ ∃ k, a = MulAut.conj k)
    {D : Subgroup a.fixedSubgroup} (hD : IsComponent a.fixedSubgroup D)
    (e : D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) : p = 7 := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = p := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj p 1 (by omega) (by simpa only [pow_one] using hE)
      (by simpa only [pow_one] using hconj)
  obtain ⟨f⟩ := HermitianForm.OddInvolutionNormalization.fixed_equiv_orthogonal
    J hp ho hE hfixed a (ha ▸ pow_orderOf_eq_one a) hout
  exact TernaryOrthogonal.prime_eq_seven_of_component (F := FixedBy.subfield E J.conj)
    hp ho hfixed (hD.map_equiv f)
    ((D.equivMapOfInjective f.toMonoidHom f.injective).symm.trans e)
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
