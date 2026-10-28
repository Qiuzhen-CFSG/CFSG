module
public import Theory.Representation.BinaryOffender.IrreducibleDiagonal
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness

/-!
# Movement on the fixed space of a commuting two-group

A two-group acting on a nonzero finite binary space has a nonzero fixed
vector. If it commutes with a fixed-free subgroup X, that fixed space is
X-invariant. An actor A with `[X,A]=X` cannot fix it pointwise: otherwise
the commutator fixes the space, contradicting the vanishing X-fixed space.

This supplies the genuine movement premise for D.2.7 on the centralizer
fixed space in the exchanged Suzuki branch of D.3.9(2). The source actor
and its centralizer are instantiated in Chapter 10 SeedAnalysis.
Source: Aschbacher--Smith, printed pp.179--180,200--201.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Nontrivial V]

/-- The fixed space of a commuting two-group is moved by A whenever
`[X,A]=X` and X has no fixed vectors. -/
theorem fixedSpace_moved_of_commutator_eq
    (ρ : Representation (ZMod 2) G V) (X A C : Subgroup G)
    (hC : IsPGroup 2 C) (hXC : X ≤ centralizer (C : Set G))
    (hfix : fixedSpace ρ X = ⊥) (hXA : ⁅X,A⁆ = X) :
    subspaceCommutator ρ (fixedSpace ρ C) A ≠ ⊥ := by
  let : MulAction C V := {
    smul c v := ρ c v
    one_smul v := by change ρ 1 v = v; simp
    mul_smul c d v := by
      change ρ ((c : G) * d) v = ρ c (ρ d v)
      simp only [map_mul,Module.End.mul_apply] }
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hd : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact dvd_pow_self 2 Module.finrank_pos.ne'
  obtain ⟨v,hv,hv0⟩ := hC.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hd
    (a := (0 : V)) (by intro c; exact map_zero (ρ c))
  have hvC : v ∈ fixedSpace ρ C := hv
  have hX : X ≤ subspaceStabilizer ρ (fixedSpace ρ C) := by
    apply le_subspaceStabilizer
    intro x hx w hw c
    change ρ (c : G) (ρ x w) = ρ x w
    rw [←Module.End.mul_apply,←map_mul,hXC hx c c.property,map_mul,Module.End.mul_apply]
    exact congrArg (ρ x) (hw c)
  intro hzero
  have hCA := (subspaceCommutator_eq_bot_iff ρ (fixedSpace ρ C) A).mp hzero
  have hCX := le_fixedSpace_commutator_of_invariant ρ hX hCA
  rw [hXA,hfix] at hCX
  exact hv0 (hCX hvC).symm
end Representation.BinaryOffender
