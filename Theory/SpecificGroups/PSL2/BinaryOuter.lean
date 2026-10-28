module
public import Theory.SpecificGroups.PSL2.BorelCoprimeFieldAction
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms

/-!
# The actual binary PSL₂ outer quotient

Inner-field coverage makes the coefficient automorphism homomorphism onto
Aut(PSL₂)/Inn(PSL₂). The finite-field automorphism group is cyclic, so this
literal outer quotient is cyclic and its solvability transports through a
specified group equivalence.

Source: GLS3, Theorem 2.5.12; the marked natural-row application is
Aschbacher--Smith 14.6.15, printed p.1035.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2
open Atlas.RankOneFieldAutomorphisms
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear

theorem binary_outer_isCyclic (F : Type*) [Field F] [Finite F] [CharP F 2] :
    IsCyclic (MulAut.Outer PSL(2,F)) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(2,F))
  let f := q.comp (pslFieldAction (F := F))
  let : IsCyclic (F ≃+* F) := OuterSolvable.finiteFieldAut_isCyclic
  apply isCyclic_of_surjective f
  intro x
  obtain ⟨α,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup PSL(2,F)) x
  obtain ⟨g,σ,hα⟩ := exists_inner_field F α
  refine ⟨σ,?_⟩
  have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
  change q (Atlas.fieldEquivPSL 2 σ) = q α
  rw [hα,map_mul,hg,one_mul]

theorem binary_outer_isSolvable_of_mulEquiv {C : Type*} [Group C]
    (F : Type*) [Field F] [Finite F] [CharP F 2] (e : C ≃* PSL(2,F)) :
    Group.IsSolvable (MulAut.Outer C) := by
  let : IsCyclic (MulAut.Outer PSL(2,F)) := binary_outer_isCyclic F
  let := IsCyclic.commGroup (α := MulAut.Outer PSL(2,F))
  exact MulAut.isSolvable_outer_of_mulEquiv e
end Theory.PSL2
