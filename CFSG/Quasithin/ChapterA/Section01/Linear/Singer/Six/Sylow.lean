module

public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow

/-!
# The seven-local structure of the binary six-dimensional linear group

The order formula for the actual general linear group gives seven-part 49.
Thus its Sylow seven-subgroups have prime-square order and are abelian.
Every seven-subgroup inherits commutativity. Regularity also gives the
Singer subgroup order 63 and hence an actual subgroup of order seven.

These are the elementary model inputs in Aschbacher–Smith A.1.12,
printed p.22. No group-family recognition premise is used.
-/

namespace CFSG.Quasithin.ChapterA.Singer.Six

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The order of the actual binary linear group in dimension six. -/
public theorem card_linearGroup (hn : Module.finrank (ZMod 2) V = 6) :
    Nat.card (V ≃ₗ[ZMod 2] V) = 20158709760 := by
  let e : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hn)
  let f : (V ≃ₗ[ZMod 2] V) ≃* Matrix.GeneralLinearGroup (Fin 6) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
        Matrix.GeneralLinearGroup.toLin.symm)
  rw [Nat.card_congr f.toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

/-- Sylow seven-subgroups have order 49, rather than merely seven-rank two. -/
public theorem card_sylow_seven (hn : Module.finrank (ZMod 2) V = 6)
    (S : Sylow 7 (V ≃ₗ[ZMod 2] V)) : Nat.card S = 7 ^ 2 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Finite (V ≃ₗ[ZMod 2] V) := Nat.finite_of_card_ne_zero (by
    rw [card_linearGroup hn]; decide)
  rw [S.card_eq_multiplicity, card_linearGroup hn]
  decide +kernel

/-- Every seven-subgroup of GL₆(2) is abelian. -/
public theorem seven_subgroup_commutative (hn : Module.finrank (ZMod 2) V = 6)
    (P : Subgroup (V ≃ₗ[ZMod 2] V)) (hP : IsPGroup 7 P) : IsMulCommutative P := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  let : IsMulCommutative S :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (card_sylow_seven hn S)
  exact .of_comm fun (a b : P) => Subtype.ext
    (congrArg (fun s : S => (s : V ≃ₗ[ZMod 2] V)) (IsMulCommutative.is_comm.comm
      (⟨a, hPS a.property⟩ : S) ⟨b, hPS b.property⟩))

/-- A regular subgroup in dimension six has order 63. -/
public theorem card_regular (hn : Module.finrank (ZMod 2) V = 6)
    {X : Subgroup (V ≃ₗ[ZMod 2] V)} (hX : LinearGroup.IsRegularOnNonzero X) :
    Nat.card X = 63 := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  rw [hX.card_eq_pow_finrank_sub_one, Nat.card_zmod, hn]
  norm_num

/-- The order-seven subgroup used in the exceptional Singer argument exists
inside the given actor, with containment in the original linear group. -/
public theorem exists_seven_subgroup (hn : Module.finrank (ZMod 2) V = 6)
    {X : Subgroup (V ≃ₗ[ZMod 2] V)} (hX : LinearGroup.IsRegularOnNonzero X) :
    ∃ W : Subgroup (V ≃ₗ[ZMod 2] V), W ≤ X ∧ Nat.card W = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Finite X := Nat.finite_of_card_ne_zero (by rw [card_regular hn hX]; decide)
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 7
    (n := 1) (by rw [card_regular hn hX]; decide)
  refine ⟨W.map X.subtype, Subgroup.map_subtype_le W, ?_⟩
  rw [Subgroup.card_map_of_injective Subtype.val_injective]
  exact hW

end CFSG.Quasithin.ChapterA.Singer.Six
