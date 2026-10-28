module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The standard involution centralizer in the Thompson matrix carrier

The first ATLAS matrix has exact order two, and its centralizer is proper:
the second matrix does not commute with it. These facts use only the checked
matrix generator certificates, independently of ambient order and simplicity.

GLS3, Table 5.3x, identifies the involution centralizer as an extension of an
extraspecial group of order 2⁹ by A₉. Constructing that quotient in this
carrier is a separate obligation; no identification is asserted here.
-/

namespace Thompson.InvolutionCentralizer

/-- The standard source generator is an actual involution. -/
public theorem orderOf_generatorA : orderOf Thompson.generatorA = 2 := by
  apply orderOf_eq_prime Thompson.generatorA_sq
  intro h
  exact Thompson.generator_mul_ne (by simp [h])

/-- The centralizer of the certified involution. -/
@[expose] public def subgroup : Subgroup Model :=
  Subgroup.centralizer ({Thompson.generatorA} : Set Model)

/-- Noncommutation of the source pair makes this a proper subgroup. -/
public theorem subgroup_ne_top : subgroup ≠ ⊤ := by
  intro h
  have hb : Thompson.generatorB ∈ subgroup := by rw [h]; trivial
  exact Thompson.generator_mul_ne
    (Subgroup.mem_centralizer_singleton_iff.mp hb).symm

end Thompson.InvolutionCentralizer
