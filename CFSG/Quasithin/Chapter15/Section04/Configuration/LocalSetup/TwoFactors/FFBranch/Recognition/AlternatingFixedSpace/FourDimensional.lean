module

public import Theory.LinearAlgebra.BinaryFourFixedSpace
public import Theory.Representation.CubicFixedSpace
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Cubic witnesses for every faithful four-dimensional A₇ action

The explicit element (0 1 2 3)(4 5) has order four. Faithfulness and the
binary hyperplane calculation show that its fixed space has dimension at
most two. The faithful image has order 2520 in GL₄(2), so pointwise
stabilizer counting supplies a nonidentity cubic element fixing this space.
Sylow containment and conjugacy then supply the required witness for every
Sylow two-subgroup.

This treats all faithful four-dimensional representations directly. It
neither identifies inequivalent actions by dimension nor uses the
six-dimensional deleted-permutation action. Trivial summands can be added
by `sylow_fixedSpace_enlargement_of_cubic_quotient` in the parent assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.4.2(7), printed p.86; B.5.1, p.99; the alternating
module comparison in Lemma 15.4.18, p.1163.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.AlternatingFixedSpace
open Module Subgroup BinaryFourFixedSpace
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private def fourCycle : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    change Equiv.Perm.sign _ = 1
    decide⟩

private theorem fourCycle_four : fourCycle ^ 4 = 1 := by decide
private theorem fourCycle_sq_ne : fourCycle ^ 2 ≠ 1 := by decide

private theorem fourCycle_two : IsPGroup 2 (Subgroup.zpowers fourCycle) := by
  apply IsPGroup.of_card_dvd_pow (n := 2)
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one fourCycle_four

private noncomputable def linearAction
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V) :
    alternatingGroup (Fin 7) →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom

omit [FiniteDimensional (ZMod 2) V] in
private theorem linearAction_injective
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hρ : Function.Injective ρ) : Function.Injective (linearAction ρ) := by
  intro g h he
  apply hρ
  exact congrArg (fun e : V ≃ₗ[ZMod 2] V => e.toLinearMap) he

open Representation.BinaryOffender

private theorem fixed_fourCycle_finrank
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hρ : Function.Injective ρ) (hdim : finrank (ZMod 2) V = 4) :
    finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers fourCycle)) ≤ 2 := by
  let W := fixedSpace ρ (Subgroup.zpowers fourCycle)
  by_contra h
  change ¬ finrank (ZMod 2) W ≤ 2 at h
  have hcodim : finrank (ZMod 2) (V ⧸ W) ≤ 1 := by
    have hsum := W.finrank_quotient_add_finrank
    rw [hdim] at hsum
    omega
  let a : pointwiseFixer W := ⟨linearAction ρ fourCycle,
    fun v hv => hv ⟨fourCycle, Subgroup.mem_zpowers fourCycle⟩⟩
  have hsq := congrArg Subtype.val (pointwiseFixer_sq W hcodim a)
  change (linearAction ρ fourCycle) ^ 2 = 1 at hsq
  apply fourCycle_sq_ne
  apply linearAction_injective ρ hρ
  simpa only [map_pow, map_one] using hsq

/-- Every faithful binary four-dimensional A₇ action has a cubic element
outside any prescribed Sylow two-subgroup fixing its entire fixed space. -/
theorem four_dimensional_enlargement
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hρ : Function.Injective ρ) (hdim : finrank (ZMod 2) V = 4)
    (S : Sylow 2 (alternatingGroup (Fin 7))) :
    ∃ d : alternatingGroup (Fin 7), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup _), ρ d v = v := by
  let f := linearAction ρ
  have hf : Function.Injective f := linearAction_injective ρ hρ
  have hcard : Nat.card f.range = 2520 := by
    change Nat.card (Set.range f) = 2520
    rw [← Nat.card_congr (Equiv.ofInjective f hf)]
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  let W := fixedSpace ρ (Subgroup.zpowers fourCycle)
  have h3 := three_dvd_intersection hdim f.range hcard W
    (fixed_fourCycle_finrank ρ hρ hdim)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨d, hd⟩ := a.property.1
  have hd3 : d ^ 3 = 1 := by
    apply hf
    rw [map_pow, map_one, hd]
    exact congrArg Subtype.val (ha ▸ pow_orderOf_eq_one a)
  have hdne : d ≠ 1 := by
    intro he
    have haone : a = 1 := Subtype.ext (hd.symm.trans (he ▸ f.map_one))
    rw [haone, orderOf_one] at ha
    omega
  apply sylow_fixedSpace_enlargement_of_cubic ρ _ fourCycle_two d hd3 hdne _ S
  intro v hv
  change f d v = v
  rw [hd]
  exact a.property.2 v hv

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.AlternatingFixedSpace
