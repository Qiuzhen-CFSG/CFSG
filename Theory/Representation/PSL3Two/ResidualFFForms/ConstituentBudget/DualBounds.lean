module

public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.Dimension
public import Theory.Representation.QuadraticDuality
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.PSL3Two.SmallModuleProperties

/-!
# The combined cost of the natural and dual-natural modules

The displacement of a faithful actor embeds it, as a set, into the linear maps
from the fixed-space quotient to the commutator space. Counting these maps and
using duality gives `rank A ≤ fixedCodim W A * fixedCodim W.dual A`. For a
nontrivial elementary two-subgroup of SL₃(2), both costs are positive and its
rank is at most two. The product bound then forces their sum above that rank.
All fixed codimensions here use the same actor.

Adapted from the Chapter C `ExtensionControl/DualExclusion.lean` argument,
without importing that higher layer. Source: Aschbacher–Smith B.4.9(2)(ii)
and B.5.1, printed pp.92,94,100–101 of the combined manuscript of 1 March 2004;
the constituent use in Meierfrankenfeld–Stellmacher (1993), (3.8), p.878.
-/

public section
open Representation Representation.BinaryOffender
namespace BinaryLinearThree.ResidualFFForms.ConstituentBudget

private theorem rank_le_fixedCodim_mul_dual
    {G W : Type*} [_root_.Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) G W)
    (hσ : Function.Injective σ) (A : Subgroup G) :
    rank A ≤ fixedCodim σ A * fixedCodim σ.dual A := by
  let τ := σ.comp A.subtype
  let U := fixedSpace σ A
  let C := Coinvariants.ker τ
  let d (a : A) : W →ₗ[ZMod 2] C :=
    (σ a - LinearMap.id).codRestrict C (fun v => Coinvariants.sub_mem_ker (ρ := τ) a v)
  let D (a : A) : (W ⧸ U) →ₗ[ZMod 2] C := U.liftQ (d a) (by
    intro v hv
    apply Subtype.ext
    exact sub_eq_zero.mpr (hv a))
  have hinj : Function.Injective D := by
    intro a b h
    apply Subtype.ext
    apply hσ
    apply LinearMap.ext
    intro v
    have he := congrArg (fun f : (W ⧸ U) →ₗ[ZMod 2] C => (f (U.mkQ v) : W)) h
    change σ a v - v = σ b v - v at he
    exact sub_left_injective he
  let : Finite ((W ⧸ U) →ₗ[ZMod 2] C) := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective D hinj
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (W ⧸ U) →ₗ[ZMod 2] C), Nat.card_zmod,
    Module.finrank_linearMap] at hc
  have hd : fixedCodim σ.dual A = Module.finrank (ZMod 2) C :=
    finrank_dual_quotient_invariants τ
  have hl := Nat.log_monotone (b := 2) hc
  rw [Nat.log_pow (by decide : 1 < 2)] at hl
  rw [hd]
  exact hl


/-- The natural module and its dual cannot share the budget of an offender. -/
theorem rank_lt_natural_add_dual_fixedCodim (A : Subgroup BinaryLinearThree.Group)
    (hA : IsElementaryTwo A) :
    rank A < fixedCodim BinaryLinearThree.W A + fixedCodim BinaryLinearThree.W.dual A := by
  have hr := elementary_rank_le_two A hA.2
  have hn := fixedCodim_pos_of_faithful BinaryLinearThree.W BinaryLinearThree.natural_injective hA.1
  have hd := fixedCodim_pos_of_faithful BinaryLinearThree.W.dual BinaryLinearThree.dual_injective hA.1
  have hp := rank_le_fixedCodim_mul_dual BinaryLinearThree.W BinaryLinearThree.natural_injective A
  by_contra! h
  have he1 : fixedCodim BinaryLinearThree.W A = 1 := by omega
  have he2 : fixedCodim BinaryLinearThree.W.dual A = 1 := by omega
  rw [he1, he2] at hp
  omega

end BinaryLinearThree.ResidualFFForms.ConstituentBudget
