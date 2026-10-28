module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.FinCases

/-!
# Two identical natural SL₃(2) summands

Coordinates are multiplicative additive-group coordinates and the action is
actual column multiplication by the same matrix on both summands. A matrix
with invertible difference from the identity proves generation by
commutators and absence of fixed points. No module classification is used.

Source: the doubled-natural hypothesis in C.1.37, printed pp.141–143.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
open Subgroup
open scoped Matrix commutatorElement
abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
abbrev DoubleSpace := Fin 2 → Fin 3 → ZMod 2

private def mover : SL := ⟨!![0,0,1;1,0,1;0,1,0], by decide⟩
private def pre (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  ![v 1 + v 2, v 0 + v 1, v 0 + v 1 + v 2]

private theorem mover_pre : ∀ v : Fin 3 → ZMod 2,
    Matrix.mulVec mover.val (pre v) - pre v = v := by decide
private theorem mover_fixed : ∀ v : Fin 3 → ZMod 2,
    Matrix.mulVec mover.val v = v → v = 0 := by decide

variable {K : Type*} [Group K] (U L : Subgroup K) [U.Normal]
    (ρ : K →* SL) (e : U ≃* Multiplicative DoubleSpace)
    (hact : ∀ k u, Multiplicative.toAdd (e (MulAut.conjNormal k u)) =
      fun j => Matrix.mulVec (ρ k).val (Multiplicative.toAdd (e u) j))
    (hL : Function.Surjective (ρ.comp L.subtype))

omit [U.Normal] in
include e in
/-- The actual doubled-natural carrier has order 64. -/
theorem doubled_card : Nat.card U = 64 := by
  rw [Nat.card_congr e.toEquiv]
  change Nat.card DoubleSpace = 64
  simp [DoubleSpace]

include hact hL in
/-- Surjectivity on the actor proves generation by commutators. -/
theorem doubled_commutator : ⁅U,L⁆ = U := by
  apply le_antisymm (commutator_le_left U L)
  obtain ⟨l,hl⟩ := hL mover
  intro u hu
  let u' : U := ⟨u,hu⟩
  let v : U := e.symm (Multiplicative.ofAdd (fun j => pre (Multiplicative.toAdd (e u') j)))
  have heq : MulAut.conjNormal (l : K) v * v⁻¹ = u' := by
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hact, ← sub_eq_add_neg]
    change (fun j => Matrix.mulVec (ρ l).val (Multiplicative.toAdd (e v) j)) -
      Multiplicative.toAdd (e v) = Multiplicative.toAdd (e u')
    have hv : Multiplicative.toAdd (e v) = fun j => pre (Multiplicative.toAdd (e u') j) := by
      simp [v]
    rw [hv, show ρ l = mover from hl]
    funext j
    exact mover_pre _
  have hcomm : ⁅(l : K),(v : K)⁆ = u := congrArg Subtype.val heq
  rw [← hcomm, commutator_comm U L]
  exact commutator_mem_commutator l.property v.property

include hact hL in
/-- The same actor has no nonidentity fixed point in either summand. -/
theorem doubled_fixed : U ⊓ centralizer (L : Set K) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro u ⟨hu,hc⟩
  obtain ⟨l,hl⟩ := hL mover
  let u' : U := ⟨u,hu⟩
  have hconj : MulAut.conjNormal (l : K) u' = u' := by
    apply Subtype.ext
    change (l : K) * u * (l : K)⁻¹ = u
    rw [mem_centralizer_iff.mp hc l l.property, mul_inv_cancel_right]
  have he := hact (l : K) u'
  rw [hconj, show ρ l = mover from hl] at he
  have hz : Multiplicative.toAdd (e u') = 0 := by
    funext j
    exact mover_fixed _ (congrFun he j).symm
  have hu1 : u' = 1 := e.injective (by
    apply Multiplicative.toAdd.injective
    simpa using hz)
  exact congrArg Subtype.val hu1

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
