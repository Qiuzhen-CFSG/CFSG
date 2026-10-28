module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Solvable.Elementary
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Constituent degrees for the remaining solvable actor

A p-group with p > 3 acts trivially in binary degree at most two, since the
orders of GL₀(2), GL₁(2), and GL₂(2) divide six. A trivial constituent for a
normal subgroup supplies an ambient invariant vector. Ambient irreducibility
and faithfulness then contradict nontriviality of that normal subgroup.
This supplies the degree hypothesis of 15.3.57(2) in the solvable branch,
without assuming the conclusion of that lemma.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1149.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

private theorem small_binary_pGroup_trivial [FiniteDimensional (ZMod 2) W]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hG : IsPGroup p G)
    (ρ : Representation (ZMod 2) G W) (hd : Module.finrank (ZMod 2) W ≤ 2) :
    ∀ g, ρ g = 1 := by
  let n := Module.finrank (ZMod 2) W
  let b := Module.finBasis (ZMod 2) W
  let φ : G →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hcard : Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) ∣ 6 := by
    have hc : ∀ m : ℕ, m ≤ 2 →
        Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) ∣ 6 := by
      intro m hm
      rw [Matrix.card_GL_field]
      interval_cases m <;> norm_num [Fin.prod_univ_succ]
    exact hc n hd
  have hp6 : ¬ p ∣ 6 := by
    intro hh
    have : p ∣ 2 ∨ p ∣ 3 := (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp hh
    rcases this with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 2) h; omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h; omega
  have hpc := (hG.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective).card_eq_or_dvd
  have htriv : φ.range = ⊥ := Subgroup.card_eq_one.mp
    (hpc.resolve_right (fun hh => hp6 (hh.trans (φ.range.card_subgroup_dvd_card.trans hcard))))
  intro g
  have hg : φ g = 1 := by
    have hh : φ g ∈ φ.range := ⟨g, rfl⟩
    rwa [htriv] at hh
  have hg' := congrArg (Matrix.GeneralLinearGroup.toLin' b) hg
  have he : ρ.asGroupHom g = 1 := by simpa only [φ, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.apply_symm_apply, map_one] using hg'
  exact congrArg Units.val he

/-- Every simple constituent of a nontrivial normal p-subgroup, p > 3, has binary degree at least three in a faithful irreducible ambient action. -/
theorem normal_pGroup_constituent_finrank_ge_three [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hρ : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (K : Subgroup G) [K.Normal] (hne : K ≠ ⊥)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hK : IsPGroup p K)
    (A : Subrepresentation (ρ.comp K.subtype)) (hA : A.toRepresentation.IsIrreducible) :
    3 ≤ Module.finrank (ZMod 2) A.toSubmodule := by
  by_contra! hd
  have ht := small_binary_pGroup_trivial hp hK A.toRepresentation (by omega)
  let := hρ
  let := hA
  let := Subrepresentation.irreducible_module_nontrivial A.toRepresentation
  obtain ⟨a, ha⟩ := exists_ne (0 : A.toSubmodule)
  have ha0 : (a : W) ≠ 0 := fun hh => ha (Subtype.ext hh)
  have hfix : Representation.invariants (ρ.comp K.subtype) ≠ ⊥ := by
    intro hb
    have hm : (a : W) ∈ Representation.invariants (ρ.comp K.subtype) := by
      intro k
      exact congrArg Subtype.val (LinearMap.congr_fun (ht k) a)
    rw [hb] at hm
    exact ha0 hm
  have hk := Representation.le_ker_of_normal_invariants_ne_bot ρ K hfix
  rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf] at hk
  exact hne (le_bot_iff.mp hk)
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

