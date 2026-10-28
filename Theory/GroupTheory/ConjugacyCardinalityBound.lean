module
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Index

/-!
# A centralizer bound from distinct conjugates

An injective finite family of conjugates embeds in the conjugation orbit.
Orbit-stabilizer bounds the centralizer order without any exhaustion or
centralizer-structure assumption. This is used by the concrete Mathieu
fixed-order exclusions in Aschbacher–Smith E.6.23.
-/

open Subgroup
namespace Theory.GroupTheory
public theorem card_mul_le_of_injective_conjugates {G : Type*} [Group G] [Finite G]
    {n : ℕ} (x : G) (f : Fin n → G) (hf : Function.Injective f)
    (hc : ∀ i, IsConj x (f i)) :
    Nat.card (centralizer ({x} : Set G)) * n ≤ Nat.card G := by
  let F : Fin n → MulAction.orbit (ConjAct G) x := fun i => ⟨f i, by
    obtain ⟨g, hg⟩ := isConj_iff.mp (hc i)
    exact ⟨ConjAct.toConjAct g, hg⟩⟩
  have hn : n ≤ Nat.card (MulAction.orbit (ConjAct G) x) := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective F
      (fun i j h => hf (congrArg Subtype.val h))
  have hi : (centralizer ({x} : Set G)).index =
      Nat.card (MulAction.orbit (ConjAct G) x) := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    calc
      _ = (MulAction.stabilizer (ConjAct G) x).index :=
        Subgroup.index_comap_of_surjective
          (MulAction.stabilizer (ConjAct G) x)
          (f := ConjAct.toConjAct.toMonoidHom) ConjAct.toConjAct.surjective
      _ = _ := MulAction.index_stabilizer (ConjAct G) x
  rw [← hi] at hn
  exact (Nat.mul_le_mul_left _ hn).trans_eq (centralizer ({x} : Set G)).card_mul_index
end Theory.GroupTheory
