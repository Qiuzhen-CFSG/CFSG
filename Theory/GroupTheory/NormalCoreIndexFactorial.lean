module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.IndexNormal

/-!
# A factorial obstruction to a trivial prime core

If a finite group has a p-subgroup of index n and its order does not divide
n!, its p-core is nontrivial. The coset action has kernel the normal core
of the subgroup. A trivial p-core would make this action faithful.

This elementary coset-action argument supplies the two-local containment
step in the HS case of Aschbacher–Smith, Proposition 1.3.4, printed p.511.
-/

namespace Theory.GroupTheory
open Subgroup

/-- Failure of the coset-action divisibility bound forces a nontrivial p-core. -/
public theorem pCore_ne_bot_of_not_card_dvd_factorial_index
    {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Subgroup G)
    (hp : IsPGroup p P) (h : ¬ Nat.card G ∣ P.index.factorial) :
    pCore p G ≠ ⊥ := by
  intro hc
  have hn : P.normalCore ≤ pCore p G :=
    le_sSup ⟨inferInstance, hp.to_le P.normalCore_le⟩
  have hb : P.normalCore = ⊥ := le_bot_iff.mp (hc ▸ hn)
  apply h
  have hd : P.normalCore.index ∣ P.index.factorial := by
    rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
    exact card_subgroup_dvd_card (MulAction.toPermHom G (G ⧸ P)).range
  rwa [hb, index_bot] at hd

end Theory.GroupTheory
