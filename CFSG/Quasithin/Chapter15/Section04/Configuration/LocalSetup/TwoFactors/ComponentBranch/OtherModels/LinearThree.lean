module

public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.PSL3.SylowFixedActions.Coverage
public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard
public import Theory.GroupAction.FourGroupOddCenter
public import Mathlib.GroupTheory.Sylow

/-!
# The linear-three fixed-action obstruction

In the linear alternatives of F.6.18(10)–(11), the restrictions
`p ≡ ±3 mod 8` and `p ≡ ε mod 4`, with `ε = +1`, say exactly `p ≡ 5 mod 8`.
The component is the actual `SL₃(p)` or `PSL₃(p)` carrier, also when it occurs
inside the graph extension.

The special group with nontrivial center is excluded by the four-group
odd-center argument. When its center is trivial, the natural projective
projection is an isomorphism. Transporting both the action and the Sylow
subgroup through this map reduces the remaining special-group case to the
projective case.

For the projective group, odd-prime automorphism coverage puts every actor in
the concrete standard automorphism subgroup. The standard Sylow-fixing
calculation then excludes a faithful four-group action: after Sylow conjugacy,
the pointwise fixer of two diagonal order-four elements and a coordinate
interchange lies in a cyclic torus. This discharges the projective rigidity
premise and proves both intrinsic linear alternatives. Quantification over
all actions also covers the component's occurrence in the graph extension.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.18(10)–(11), printed pp.309–310, and 15.4.18,
printed pp.1162–1163. The parent owns the compatible component action and
transport from the ambient quotient.
-/

open scoped MatrixGroups
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels

/-- The linear sign in the source selects exactly the residue five modulo eight. -/
public theorem linearThree_prime_restrictions_iff (p : ℕ) :
    ((p % 8 = 3 ∨ p % 8 = 5) ∧ p % 4 = 1) ↔ p % 8 = 5 := by omega

/-- A nontrivial scalar center excludes the required fixed-subgroup
configuration on the actual special linear group. No faithfulness or Sylow
condition is needed for this branch. -/
public theorem linearThree_special_nontrivial_center_fixed_action_obstruction
    (p : ℕ) [Fact p.Prime]
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hZ : center SL(3, ZMod p) ≠ ⊥)
    (hA : Nat.card A = 4) (ρ : A →* MulAut SL(3, ZMod p)) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup :=
  Theory.GroupAction.exists_fixedSubgroup_not_selfCentralizing_twoCore_of_odd_center
    (Matrix.SL3.odd_card_center (ZMod p)) hZ hA ρ

/-- Projective Sylow-fixing rigidity suffices for the entire special linear
alternative. The nontrivial-center branch uses its actual odd center; the
trivial-center branch transports through the canonical projection. This is
a conditional reduction; the projective premise is discharged below. -/
public theorem linearThree_special_fixed_action_obstruction_of_projective_rigidity
    (p : ℕ) [Fact p.Prime]
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hprojective : ∀ (Q : Sylow 2 PSL(3, ZMod p)) (σ : A →* MulAut PSL(3, ZMod p)),
      (∀ a : A, ∀ x : Q, σ a x = x) → ¬ Function.Injective σ)
    (P : Sylow 2 SL(3, ZMod p)) (hA : Nat.card A = 4)
    (ρ : A →* MulAut SL(3, ZMod p)) (hinj : Function.Injective ρ)
    (hfixed : ∀ a : A, ∀ x : P, ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  classical
  by_cases hZ : center SL(3, ZMod p) = ⊥
  · let e := Matrix.SL3.equivProjectiveOfCenterEqBot (ZMod p) hZ
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    let σ := (MulAut.congr e).toMonoidHom.comp ρ
    have hfix : ∀ a : A, ∀ y : Q, σ a y = y := by
      intro a y
      obtain ⟨x, hx, hxy⟩ := y.property
      change e x = (y : PSL(3, ZMod p)) at hxy
      change e (ρ a (e.symm y)) = y
      rw [← hxy, e.symm_apply_apply, hfixed a ⟨x, hx⟩]
    exact (hprojective Q σ hfix ((MulAut.congr e).injective.comp hinj)).elim
  · exact linearThree_special_nontrivial_center_fixed_action_obstruction p hZ hA ρ

/-- No faithful four-group action on the actual projective linear group fixes
a Sylow two-subgroup pointwise. Coverage and the standard-action calculation
are both discharged; no automorphism classification premise remains. -/
public theorem linearThree_projective_no_faithful_sylow_fixed_action
    (p : ℕ) [Fact p.Prime] (hp : p % 8 = 5)
    (P : Sylow 2 PSL(3, ZMod p))
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (ρ : A →* MulAut PSL(3, ZMod p))
    (hfixed : ∀ a : A, ∀ x : P, ρ a x = x) : ¬ Function.Injective ρ := by
  apply Matrix.PSL3.SylowFixedActions.Standard.not_injective p hp P hA ρ ?_ hfixed
  intro a
  have ha : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A) a
  apply Matrix.PSL3.SylowFixedActions.mem_standard_of_involutive_of_fixes_sylow
    p hp P (ρ a) ?_ (hfixed a)
  rw [← map_pow, ha, map_one]

/-- The projective linear alternative in the fixed-subgroup interface used by
the component branch. The stronger rigidity theorem already excludes the
faithful action. The centralizer and two-core are internal to the fixed subgroup. -/
public theorem linearThree_projective_fixed_action_obstruction
    (p : ℕ) [Fact p.Prime] (hp : p % 8 = 5)
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 PSL(3, ZMod p)) (hA : Nat.card A = 4)
    (ρ : A →* MulAut PSL(3, ZMod p)) (hinj : Function.Injective ρ)
    (hfixed : ∀ a : A, ∀ x : P, ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup :=
  (linearThree_projective_no_faithful_sylow_fixed_action p hp P hA ρ hfixed hinj).elim

/-- The special linear alternative, retaining its actual scalar center.
A nontrivial center gives the odd-center obstruction; otherwise the canonical
projective comparison transports the action to the excluded projective case. -/
public theorem linearThree_special_fixed_action_obstruction
    (p : ℕ) [Fact p.Prime] (hp : p % 8 = 5)
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 SL(3, ZMod p)) (hA : Nat.card A = 4)
    (ρ : A →* MulAut SL(3, ZMod p)) (hinj : Function.Injective ρ)
    (hfixed : ∀ a : A, ∀ x : P, ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup :=
  linearThree_special_fixed_action_obstruction_of_projective_rigidity p
    (fun Q σ hfix => linearThree_projective_no_faithful_sylow_fixed_action
      p hp Q hA σ hfix) P hA ρ hinj hfixed

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels
