module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.NormNum

/-!
# The natural orthogonal actor in the local core calculation

The literal group SL₂(2) wr C₂ has order 72 and trivial two-core.
Every element of its two-core has eighth power one. Normality puts its
commutators with the two coordinate cubic actors in that same core.
A kernel-checked calculation on the 72 actors shows that these three
power conditions force the element to be the identity.

This is the actor calculation used for Aschbacher–Smith 15.3.59,
combined manuscript (1 March 2004), printed p.1150. The actor is the
literal one in the natural action of Section 15.3, without a family tag
or an assumed quotient identification.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.LocalCore
open Subgroup
open scoped commutatorElement

private abbrev PlaneActor := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev PlaneIndex := Multiplicative (ZMod 2)
private abbrev Actor := RegularWreathProduct PlaneActor PlaneIndex

private instance : Fintype Actor := Fintype.ofEquiv
  ((PlaneIndex → PlaneActor) × PlaneIndex)
  (RegularWreathProduct.equivProd _ _).symm
private instance : DecidableEq Actor := fun a b => decidable_of_iff
  (a.left = b.left ∧ a.right = b.right) RegularWreathProduct.ext_iff.symm

private def cubic (i : PlaneIndex) : Actor :=
  ⟨fun j => if j = i then (⟨!![0,1;1,1], by decide⟩ : PlaneActor) else 1, 1⟩

private theorem actor_certificate : ∀ x : Actor,
    x ^ 8 = 1 → ⁅x, cubic 1⁆ ^ 8 = 1 →
      ⁅x, cubic (Multiplicative.ofAdd 1)⁆ ^ 8 = 1 → x = 1 := by
  decide +kernel

theorem orthogonalActor_card : Nat.card (RegularWreathProduct
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))) = 72 := by
  rw [RegularWreathProduct.card]
  have hc : Nat.card PlaneActor = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hc]
  norm_num [PlaneIndex, Nat.card_eq_fintype_card]

theorem orthogonalActor_twoCore : pCore 2 (RegularWreathProduct
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))) = ⊥ := by
  have hd : Nat.card (pCore 2 Actor) ∣ 72 :=
    orthogonalActor_card ▸ (pCore 2 Actor).card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card (pCore 2 Actor)) 9 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Actor)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 9).pow_left n
  have hd8 : Nat.card (pCore 2 Actor) ∣ 8 := hcop.dvd_mul_right.mp hd
  have he (x : Actor) (hx : x ∈ pCore 2 Actor) : x ^ 8 = 1 := by
    obtain ⟨n, hn⟩ := hd8
    have hp := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : pCore 2 Actor)))
    change x ^ Nat.card (pCore 2 Actor) = 1 at hp
    rw [hn, pow_mul, hp, one_pow]
  apply le_bot_iff.mp
  intro x hx
  apply actor_certificate x (he x hx)
  all_goals
    apply he
    simpa only [commutatorElement_def, mul_assoc] using
      (pCore 2 Actor).mul_mem hx
      ((inferInstance : (pCore 2 Actor).Normal).conj_mem _
        ((pCore 2 Actor).inv_mem hx) _)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.LocalCore
