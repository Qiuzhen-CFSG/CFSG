module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The model and action alternatives in 1.1.5(3)

This shared source interface records all six actual model/action alternatives.
Every family uses a genuine group equivalence, and the alternating alternatives
retain the specified conjugating permutation on the group or its central quotient.
The characteristic-two cases include the small derived groups and the actual
triality and Ree constructions; the sporadic case retains the two-core quotient.
These propositions specify the source conclusion and do not prove classification.

The historical public namespace is retained so existing Chapter15 consumers
continue to use exactly the same declarations. Locating the interface here lets
Chapter2 apply the earlier source statement without importing later source proofs.
The former Chapter15 module publicly reexports this module.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3),
printed pp.501--503; Theorem C and Remark A.2.4, p.33.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
open ClassificationModels Chapter1.Section02.LocalModels
variable {L : Type*} [Group L]

/-- Exactly the characteristic-two cases C(3) and C(4). -/
def LieTypeTwoModel (L : Type*) [Group L] : Prop :=
  IsBenderModel L ∨ RankTwoTheoremC L ∨
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL L n 2

/-- Conjugation by a specified permutation, on the actual alternating model
or on the central quotient of its perfect triple cover. -/
def AlternatingAction (α : MulAut L) (n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∃ e : L ≃* alternatingGroup (Fin n),
    ∀ x : L, (e (α x) : Equiv.Perm (Fin n)) = σ * e x * σ⁻¹) ∨
  (IsQuasisimple L ∧ Nonempty (center L ≃* Multiplicative (ZMod 3)) ∧
    ∃ e : (L ⧸ center L) ≃* alternatingGroup (Fin n),
      ∀ x : L, (e (QuotientGroup.mk' (center L) (α x)) : Equiv.Perm (Fin n)) =
        σ * e (QuotientGroup.mk' (center L) x) * σ⁻¹)

/-- A two-central inner automorphism: an involution in the inner automorphism
group which centralizes a Sylow two-subgroup of the original group. -/
def TwoCentralInner (α : MulAut L) : Prop :=
  α ∈ (MulAut.conj (G := L)).range ∧ orderOf α = 2 ∧
    ∃ P : Sylow 2 L, ∀ x : P, α (x : L) = x

/-- The six alternatives in 1.1.5(3), including their actions. -/
inductive ModelAction115 (L : Type*) [Group L] (α : MulAut L) : Prop
  | lie (simple : IsSimpleGroup L) (model : LieTypeTwoModel L)
      (inner : α ∈ (MulAut.conj (G := L)).range)
  | two_cover (nontrivial_center : center L ≠ ⊥) (center_eq : center L = pCore 2 L)
      (model : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 ∨
        IsG2At (L ⧸ pCore 2 L) 4)
      (inner : α ∈ (MulAut.conj (G := L)).range)
  | six (σ : Equiv.Perm (Fin 6)) (transposition : σ.IsSwap)
      (action : AlternatingAction α 6 σ)
  | seven (σ : Equiv.Perm (Fin 7)) (cycles : σ.cycleType = {2, 2, 2})
      (action : AlternatingAction α 7 σ)
  | odd (model : ClassicalGroup.IsPSL L 3 3 ∨
        ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p)
      (inner : α ∈ (MulAut.conj (G := L)).range)
  | sporadic (name : SporadicName) (not_j3 : name ≠ .j3)
      (model : Nonempty ((L ⧸ pCore 2 L) ≃* name.Carrier))
      (action : TwoCentralInner α)

/-- The automorphism in the model alternative is the actual conjugation by z
on the subgroup K of I. No ambient normality of either subgroup is asserted. -/
def HasModelAction115 {G : Type*} [Group G] {I : Subgroup G}
    (K : Subgroup I) (z : G) : Prop :=
  ∃ α : MulAut K, (∀ x : K, ((α x : I) : G) = z * (x : G) * z⁻¹) ∧
    ModelAction115 K α

end CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
