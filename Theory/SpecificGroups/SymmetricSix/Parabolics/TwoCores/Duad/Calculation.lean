module

public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic
/-!
# The duad model cores and their conjugation actions

The action of S₄ on its three double transpositions gives a surjection to S₃.
Its kernel is the Klein four group; the trivial two-core of S₃ identifies it
as the actual two-core. Kernel-checked finite calculations prove transitivity
on the three nonidentity elements and self-centralization. Adding the central
S₂ factor gives the eight-group core and the reducible invariant line.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.7,
printed pp. 420–421, including the explicit S₆ exception to irreducibility.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricSix.DuadCalculation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
abbrev Four := Equiv.Perm (Fin 4)

def doubleSwap (i : Fin 3) : Four :=
  if i = 0 then Equiv.swap 0 1 * Equiv.swap 2 3
  else if i = 1 then Equiv.swap 0 2 * Equiv.swap 1 3
  else Equiv.swap 0 3 * Equiv.swap 1 2

def doubleSwapIndex (g : Four) : Fin 3 :=
  if g = doubleSwap 0 then 0 else if g = doubleSwap 1 then 1 else 2

def onThree (g : Four) (i : Fin 3) : Fin 3 :=
  doubleSwapIndex (g * doubleSwap i * g⁻¹)

def quotientHom : Four →* Equiv.Perm (Fin 3) where
  toFun g := {
    toFun := onThree g
    invFun := onThree g⁻¹
    left_inv := by revert g; decide +kernel
    right_inv := by revert g; decide +kernel }
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem quotientHom_surjective : Function.Surjective quotientHom := by decide +kernel

abbrev core : Subgroup Four := quotientHom.ker

instance : IsElementaryAbelian 2 core where
  is_comm.comm := by decide +kernel
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)

theorem core_card : Nat.card core = 4 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem core_eq : core = pCore 2 Four :=
  ker_eq_twoCore_of_surjective_perm_three quotientHom quotientHom_surjective
    (IsElementaryAbelian.isPGroup 2 core)

theorem core_mem_iff : ∀ g : Four, g ∈ core ↔ g.sign = 1 ∧ g ^ 2 = 1 := by
  decide +kernel

theorem centralizer_core : Subgroup.centralizer (core : Set Four) = core := by
  ext g
  rw [Subgroup.mem_centralizer_iff]
  exact (show ∀ g : Four, (∀ h ∈ core, h * g = g * h) ↔ g ∈ core by decide +kernel) g

theorem core_conjugate : ∀ x ∈ core, x ≠ 1 → ∀ y ∈ core, y ≠ 1 →
    ∃ g : Four, g * x * g⁻¹ = y := by decide +kernel

theorem normal_subgroup_core (N : Subgroup Four) [N.Normal] (hle : N ≤ core) :
    N = ⊥ ∨ N = core := by
  by_cases h : N = ⊥
  · exact Or.inl h
  right
  have hex : ∃ x ∈ N, x ≠ (1 : Four) := by
    by_contra! hh
    apply h
    apply le_antisymm _ bot_le
    intro x hx
    exact hh x hx
  obtain ⟨x, hx, hne⟩ := hex
  apply le_antisymm hle
  intro y hy
  by_cases hy1 : y = 1
  · subst y; exact N.one_mem
  obtain ⟨g, rfl⟩ := core_conjugate x (hle hx) hne y hy hy1
  exact Subgroup.Normal.conj_mem inferInstance x hx g
abbrev Two := Equiv.Perm (Fin 2)

def productQuotientHom : Two × Four →* Equiv.Perm (Fin 3) :=
  quotientHom.comp (MonoidHom.snd _ _)

def productCore : Subgroup (Two × Four) := (⊤ : Subgroup Two).prod core

instance : productCore.Normal := inferInstanceAs (((⊤ : Subgroup Two).prod core).Normal)

instance : IsElementaryAbelian 2 productCore where
  is_comm.comm := by
    intro x y
    apply Subtype.ext
    apply Prod.ext
    · exact (show ∀ a b : Two, a * b = b * a by decide) _ _
    · exact congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨x.1.2, x.2.2⟩ : core) ⟨y.1.2, y.2.2⟩)
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    apply Prod.ext
    · exact (show ∀ a : Two, a ^ 2 = 1 by decide) _
    · exact elemPow_eq_one_of_isElementaryAbelian _ x.2.2

theorem productCore_card : Nat.card productCore = 8 := by
  change Nat.card ((⊤ : Subgroup Two).prod core) = 8
  rw [Nat.card_congr ((⊤ : Subgroup Two).prodEquiv core).toEquiv,
    Nat.card_prod, core_card, Nat.card_congr (Subgroup.topEquiv (G := Two)).toEquiv]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem productQuotientHom_surjective : Function.Surjective productQuotientHom := by
  intro y
  obtain ⟨x, rfl⟩ := quotientHom_surjective y
  exact ⟨(1, x), rfl⟩

theorem productQuotientHom_ker : productQuotientHom.ker = productCore := by
  ext x
  change quotientHom x.2 = 1 ↔ (True ∧ quotientHom x.2 = 1)
  simp only [true_and]

theorem productCore_eq : productCore = pCore 2 (Two × Four) := by
  have hk : IsPGroup 2 productQuotientHom.ker := by
    rw [productQuotientHom_ker]
    exact IsElementaryAbelian.isPGroup 2 productCore
  rw [← productQuotientHom_ker]
  exact ker_eq_twoCore_of_surjective_perm_three _ productQuotientHom_surjective hk

theorem centralizer_productCore :
    Subgroup.centralizer (productCore : Set (Two × Four)) = productCore := by
  ext x
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    refine ⟨Subgroup.mem_top _, ?_⟩
    change x.2 ∈ core
    rw [← centralizer_core, Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Prod.snd (hx (1, y) ⟨Subgroup.mem_top _, hy⟩)
  · intro hx y hy
    apply Prod.ext
    · exact (show ∀ a b : Two, a * b = b * a by decide) _ _
    · exact congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨y.2, hy.2⟩ : core) ⟨x.2, hx.2⟩)

def centralFactor : Subgroup (Two × Four) := (⊤ : Subgroup Two).prod ⊥

instance : centralFactor.Normal := inferInstanceAs (((⊤ : Subgroup Two).prod ⊥).Normal)

theorem centralFactor_card : Nat.card centralFactor = 2 := by
  change Nat.card ((⊤ : Subgroup Two).prod (⊥ : Subgroup Four)) = 2
  rw [Nat.card_congr ((⊤ : Subgroup Two).prodEquiv (⊥ : Subgroup Four)).toEquiv,
    Nat.card_prod, Nat.card_congr (Subgroup.topEquiv (G := Two)).toEquiv]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem centralFactor_lt_core : centralFactor < productCore := by
  apply lt_of_le_of_ne
  · exact Subgroup.prod_mono le_rfl bot_le
  · intro he
    have := congrArg Nat.card (congrArg (fun S : Subgroup (Two × Four) => ↥S) he)
    rw [centralFactor_card, productCore_card] at this
    contradiction

end Theory.SpecificGroups.SymmetricSix.DuadCalculation
