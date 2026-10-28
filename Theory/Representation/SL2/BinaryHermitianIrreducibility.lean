module
public import Theory.Representation.OrthogonalFourMinusBinaryIrreducibility
public import Theory.Representation.SL2.BinarySmallModels
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducibility of the binary Hermitian representation

The additive irreducibility theorem for the literal SL₂ congruence action
applies to every binary subrepresentation. This identifies the existing
Hermitian model as irreducible over F₂, preserving its fixed-field scalar
restriction. The source consumer is the original orthogonal-minus row of
Aschbacher--Smith10.1.1(4) and10.2.9, printed pp.741,751.
-/

public noncomputable section
namespace Representation.SL2.BinarySmall
open OrthogonalFourMinus.FiniteModel
local instance irreducibleBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (fixedField n) :=
  ZMod.algebra (fixedField n) 2
local instance irreducibleBinaryModule (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

/-- Binary irreducibility of the literal Hermitian congruence representation. -/
theorem hermitian_irreducible (n : ℕ) [NeZero n] : IsIrreducible (hermitian n) := by
  let : Nontrivial (Space n) := (coordinates n).toEquiv.nontrivial
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have h := BinaryIrreducibility.invariant_addSubgroup_eq_bot_or_top n
    S.toSubmodule.toAddSubgroup (fun g x hx => S.apply_mem_toSubmodule g hx)
  rcases h with hb | ht
  · exfalso
    apply hS
    apply Subrepresentation.toSubmodule_injective
    ext x
    change x ∈ S.toSubmodule.toAddSubgroup ↔ x = 0
    rw [hb,AddSubgroup.mem_bot]
  · apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro x _
    change x ∈ S.toSubmodule.toAddSubgroup
    rw [ht]
    trivial
end Representation.SL2.BinarySmall
