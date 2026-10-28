module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven.StandardSylow
public import Theory.PGroupCore
public import Theory.GroupAction.AutomorphismFixedTransport
public import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic

/-!
# The sign-corrected S₅ embedding in A₇

A permutation of five letters extends to an even permutation on seven letters
by applying its sign to the other two letters. This injective homomorphism
lands in the fixed subgroup of conjugation by `(0 1)`. The symmetric group
on five letters has trivial two-core: a nontrivial normal subgroup contains
A₅, whose order is divisible by three.

This supplies the fixed-subgroup model in the exclusion of the A₇ alternatives
in Aschbacher–Smith 15.4.18, printed pp.1162–1163.
-/

@[expose] public section

open Equiv Equiv.Perm Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven
abbrev S5 := Perm (Fin 5)
abbrev transpositionFixed := (MulAut.conjNormal t : MulAut K).fixedSubgroup

def signToTwo : ℤˣ →* Perm (Fin 2) where
  toFun u := if u = 1 then 1 else swap 0 1
  map_one' := by decide
  map_mul' := by decide +kernel

def blockHom : Perm (Fin 2) × S5 →* Perm (Fin 7) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 2 ⊕ Fin 5 ≃ Fin 7)).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom _ _)

def modelHom : S5 →* Perm (Fin 7) :=
  blockHom.comp ((signToTwo.comp Equiv.Perm.sign).prod (MonoidHom.id _))

lemma modelHom_even : ∀ x, modelHom x ∈ alternatingGroup (Fin 7) := by
  change ∀ x, (modelHom x).sign = 1
  decide +kernel

lemma modelHom_fixed : ∀ x, t * modelHom x * t⁻¹ = modelHom x := by
  decide +kernel

def modelToFixed : S5 →* transpositionFixed :=
  (modelHom.codRestrict _ modelHom_even).codRestrict _ (by
    intro x
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    exact modelHom_fixed x)

lemma blockHom_injective : Function.Injective blockHom :=
  (Equiv.permCongrHom _).injective.comp Equiv.Perm.sumCongrHom_injective

lemma modelToFixed_injective : Function.Injective modelToFixed := by
  intro x y h
  have hh := blockHom_injective (congrArg (fun g : transpositionFixed => g.val.val) h)
  exact congrArg Prod.snd hh


lemma s5_twoCore_eq_bot : pCore 2 S5 = ⊥ := by
  by_contra h
  have hn : Nontrivial (pCore 2 S5) := (Subgroup.nontrivial_iff_ne_bot _).2 h
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5)
    (by simp) hn
  have hp := (pCore_isPGroup (p := 2) (G := S5)).to_le hle
  obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
  have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hc] at hn
  have hd : 3 ∣ 2 ^ n := (by decide : 3 ∣ 60).trans hn
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this


end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven
