/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/SmallIndexSimple.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Perm

/-!
# Small-index subgroups of finite simple groups

The coset action of a simple group is faithful or trivial. A factorial
cardinality bound excludes faithfulness and forces the subgroup to be full.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/SmallIndexSimple.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Use ordinary local instance bindings in proposition-valued proofs.
Definitions remain exposed for the source computational interfaces.
-/

@[expose] public section

namespace Atlas.GroupTheory

/-- A proper subgroup of a finite simple group has index large enough for the
faithful coset action. No classification of subgroups is used. -/
theorem subgroup_eq_top_of_index_factorial_lt {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (H : Subgroup G) (hcard : H.index.factorial < Nat.card G) : H=⊤ := by
  classical
  let f := MulAction.toPermHom G (G ⧸ H)
  have hk : f.ker=⊤ := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · have hi := (MonoidHom.ker_eq_bot_iff f).mp h
      have hc := Nat.card_le_card_of_injective f hi
      have he : Nat.card (Equiv.Perm (G ⧸ H)) = H.index.factorial := by
        let := Fintype.ofFinite (G ⧸ H)
        rw [Nat.card_eq_fintype_card,Fintype.card_perm]
        rw [Subgroup.index_eq_card,Nat.card_eq_fintype_card]
      rw [he] at hc
      omega
    · exact h
  let : Subsingleton (G ⧸ H) := ⟨by
    intro x y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
    have hm : g ∈ f.ker := by rw [hk]; trivial
    have he : f g = 1 := hm
    have hx : g • x=x := congrArg (fun p : Equiv.Perm (G ⧸ H) => p x) he
    exact hx.symm.trans hg⟩
  apply (Subgroup.index_eq_one).mp
  rw [Subgroup.index_eq_card]
  exact Nat.card_unique

end Atlas.GroupTheory
