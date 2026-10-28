module

public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Nontrivial subgroup action on restricted submodules

Commutator generation rules out a trivial subgroup action. On a simple
module, normality then forces the subgroup fixed space to vanish. Any
nonzero subrepresentation of a restriction containing that subgroup
inherits its nontrivial action. The inclusion is the actual subgroupOf
inclusion into the restricting subgroup.

These are the action transfers used for the index-two inertia block in
the Clifford pairing argument supporting Aschbacher–Smith 13.8.21(1),
printed p.956. They do not assume or establish inertia irreducibility.
-/

public section

namespace Representation.CubicClifford
open Representation.BinaryOffender
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]

/-- Commutator generation rules out a trivial subgroup action. -/
theorem not_le_ker_of_commutator_eq_top (ρ : Representation (ZMod 2) H V)
    [Nontrivial V] (X : Subgroup H) (hX : subspaceCommutator ρ ⊤ X = ⊤) :
    ¬ X ≤ ρ.ker := by
  intro hker
  have hbot : subspaceCommutator ρ ⊤ X = ⊥ :=
    (subspaceCommutator_eq_bot_iff ρ ⊤ X).mpr (by
      intro v _ x
      have hx : ρ (x : H) = 1 := hker x.property
      change ρ (x : H) v = v
      rw [hx, Module.End.one_apply])
  exact top_ne_bot (hX.symm.trans hbot)

/-- On a simple module, generation by normal-subgroup commutators removes
all subgroup fixed vectors. -/
theorem invariants_eq_bot_of_commutator_eq_top (ρ : Representation (ZMod 2) H V)
    [IsIrreducible ρ] (X : Subgroup H) [X.Normal]
    (hX : subspaceCommutator ρ ⊤ X = ⊤) : invariants (ρ.comp X.subtype) = ⊥ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  by_contra hf
  exact not_le_ker_of_commutator_eq_top ρ X hX (le_ker_of_normal_invariants_ne_bot ρ X hf)

/-- A nonzero restricted submodule retains a nontrivial action of X if the
ambient X-fixed space is zero. This applies in particular to an inertia block. -/
theorem not_le_ker_on_subrepresentation (ρ : Representation (ZMod 2) H V)
    (I X : Subgroup H) (hXI : X ≤ I)
    (hfix : invariants (ρ.comp X.subtype) = ⊥)
    (S : Subrepresentation (ρ.comp I.subtype)) [Nontrivial S.toSubmodule] :
    ¬ X.subgroupOf I ≤ S.toRepresentation.ker := by
  intro hker
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
  have hmem : (v : V) ∈ invariants (ρ.comp X.subtype) := by
    intro x
    let xi : I := ⟨x, hXI x.property⟩
    have hx : S.toRepresentation xi = 1 := hker (show xi ∈ X.subgroupOf I from x.property)
    have he := congrArg (fun f : Module.End (ZMod 2) S.toSubmodule => (f v : V)) hx
    exact he
  rw [hfix, Submodule.mem_bot] at hmem
  exact hv (Subtype.ext hmem)

end Representation.CubicClifford
