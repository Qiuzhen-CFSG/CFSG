module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter
public import Theory.GroupTheory.Covering

/-!+# Abelian outer group of the external unitary component

For the genuine `IsPSU D 3 (2^n)` model with even `n > 1`, the diagonal
outer image is trivial and the remaining outer group is cyclic. The matrix
field has order `(2^n)^2` and conjugation is `x ↦ x^(2^n)`. The model theorem
allows the arbitrary Hermitian form stored by `IsPSU`.

The inherited quasisimplicity and trivial center give simplicity of D.
Transport along the stored multiplicative equivalence then supplies the
model's simplicity and brings its outer-group conclusion back to D. This
discharges the unitary case of the outer-commutativity input used in source
cubic generation, without any extra automorphism-coverage hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20(a), printed p.954; GLS3 Theorem 2.5.12(b,c,d,f) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.OuterAutomorphisms

/-- The actual outer automorphism group in the `ExternalCarrier.unitaryThree`
case is abelian. Quasisimplicity and centerlessness are inherited source inputs;
the genuine model equivalence discharges every matrix and coverage premise. -/
theorem unitaryThree_outer_isMulCommutative {D : Type*} [Group D] [IsQuasisimple D]
    {n : ℕ} (hn : 1 < n) (heven : Even n)
    (h : ClassicalGroup.IsPSU D 3 (2 ^ n)) (hcenter : center D = ⊥) :
    IsMulCommutative (MulAut.Outer D) := by
  have hs := IsQuasisimple.simple (G := D)
  let ec := (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  let : IsSimpleGroup D := ec.isSimpleGroup_congr.mp hs
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    e.isSimpleGroup_congr.mp inferInstance
  let := HermitianForm.EvenSemilinear.outer_isCyclic_of_even J hn heven hcard hconj
  let := (MulAut.outerCongr e).isCyclic.mpr inferInstance
  infer_instance

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.OuterAutomorphisms
