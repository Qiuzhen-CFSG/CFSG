module

public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.GroupTheory.Perm.SevenPointIndexTen

/-!
# The seven-point end of the binary component argument

For the actual automorphism action on an elementary group A of order 32,
an orbit of length thirteen is impossible: Aut(A) is GL₅(2), of order
9999360. An orbit generating A gives a faithful permutation representation
of every faithful actor. Thus an orbit of length seven or thirteen whose
point stabilizer has order 72 would give a subgroup of S₇ of order 504.

This proves the numerical and faithfulness deductions on printed p.1201
of Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 16.5.12.
The orbit lengths, generation, and stabilizer order remain geometric
premises. They must be established for N_G(A)/C_G(A) in the contained-A
branch; this module does not assert the source lemma or those premises.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary

open Subgroup MulAction
open scoped IsMulCommutative

/-- The actual group/vector-space correspondence in rank five, followed
by the ordered-basis count. -/
theorem card_automorphisms_of_elementary_thirtyTwo
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 32) : Nat.card (MulAut A) = 9999360 := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive A) = 2 ^ 5 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    change Nat.card A = _ at hsize
    simpa only [Nat.card_zmod, hA, show (2 : ℕ) ^ 5 = 32 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive A) = 5 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let autLinear : MulAut A ≃* (Additive A ≃ₗ[ZMod 2] Additive A) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let basis := Module.finBasisOfFinrankEq (ZMod 2) (Additive A) hdim
  let e : MulAut A ≃* Matrix.GeneralLinearGroup (Fin 5) (ZMod 2) := autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive A)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' basis).symm)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ, ZMod.card]

/-- A generating orbit detects every automorphism of A, not merely those
fixing a chosen basis. -/
theorem orbit_action_injective_of_generating
    {A M : Type*} [Group A] [Group M]
    [MulDistribMulAction M A] [FaithfulSMul M A]
    (z : A) (hgen : closure (orbit M z) = ⊤) :
    Function.Injective (MulAction.toPermHom M (orbit M z)) := by
  intro m n h
  have he : (MulDistribMulAction.toMulAut M A m).toMonoidHom =
      (MulDistribMulAction.toMulAut M A n).toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense hgen
    intro x hx
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨x, hx⟩)
  exact eq_of_smul_eq_smul (α := A) (fun a => DFunLike.congr_fun he a)

/-- The thirteen alternative is excluded by the genuine linear action
on A, without an assumed embedding into a group of the desired order. -/
theorem orbit_card_seven_of_seven_or_thirteen
    {A M : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group M] [Finite M] [MulDistribMulAction M A] [FaithfulSMul M A]
    (hA : Nat.card A = 32) (z : A)
    (hlen : Nat.card (orbit M z) = 7 ∨ Nat.card (orbit M z) = 13) :
    Nat.card (orbit M z) = 7 := by
  have hdiv : Nat.card M ∣ 9999360 := by
    rw [← card_automorphisms_of_elementary_thirtyTwo hA]
    apply Subgroup.card_dvd_of_injective (MulDistribMulAction.toMulAut M A)
    intro m n he
    exact eq_of_smul_eq_smul (α := A) (fun a => DFunLike.congr_fun he a)
  rcases hlen with h7 | h13
  · exact h7
  · have hcount : Nat.card (orbit M z) * Nat.card (stabilizer M z) = Nat.card M := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (orbitProdStabilizerEquivGroup M z)
    have hd13 : 13 ∣ Nat.card M := by
      rw [← hcount, h13]
      exact dvd_mul_right _ _
    have : 13 ∣ 9999360 := hd13.trans hdiv
    norm_num at this

/-- The constructed faithful seven-point action and its orbit-stabilizer
order give the last contradiction in the contained-A branch of 16.5.12. -/
theorem no_generating_orbit_with_stabilizer_72
    {A M : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group M] [Finite M] [MulDistribMulAction M A] [FaithfulSMul M A]
    (hA : Nat.card A = 32) (z : A)
    (hgen : closure (orbit M z) = ⊤)
    (hlen : Nat.card (orbit M z) = 7 ∨ Nat.card (orbit M z) = 13)
    (hstab : Nat.card (stabilizer M z) = 72) : False := by
  classical
  have hseven := orbit_card_seven_of_seven_or_thirteen hA z hlen
  have hcount : Nat.card (orbit M z) * Nat.card (stabilizer M z) = Nat.card M := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (orbitProdStabilizerEquivGroup M z)
  have hcard : Nat.card M = 504 := by
    rw [hseven, hstab] at hcount
    exact hcount.symm
  let e := Finite.equivFinOfCardEq hseven
  let f : M →* Equiv.Perm (Fin 7) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom M (orbit M z))
  exact Theory.GroupTheory.SevenPoint.no_faithful_action_of_card_504 hcard f
    (e.permCongrHom.injective.comp (orbit_action_injective_of_generating z hgen))

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary
