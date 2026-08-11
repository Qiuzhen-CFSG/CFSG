module

public import Mathlib.GroupTheory.Focal
public import Submission.FeitThompson.BGsection1.proposition_1_16
public import Submission.FeitThompson.Commutator.FocalSubgroup

open scoped Pointwise commutatorElement IsMulCommutative

/-
The focal-subgroup API is now part of Mathlib.  The original submission used
the same names, so this file keeps the one theorem from the source text and
provides the old transfer-map spelling as a thin compatibility layer.
-/

namespace Subgroup

variable {G : Type*} [Group G]

@[expose] public noncomputable def ftTransferFocal (H : Subgroup G) [H.FiniteIndex] :
    G →* H ⧸ H.focalSubgroupOf :=
  transferFocal H

public theorem ftTransferFocal_eq_pow (H : Subgroup G) [H.FiniteIndex] (x : H) :
    ftTransferFocal H x = (x : H ⧸ H.focalSubgroupOf) ^ H.index := by
  simpa [ftTransferFocal] using transferFocal_eq_pow H x

variable {p : ℕ} [Fact p.Prime] [Finite G] [Finite (Sylow p G)]

omit [Finite (Sylow p G)] in
public lemma ker_restrict_ftTransferFocal_eq_focalSubgroupOf (P : Sylow p G) :
    (((P : Subgroup G).ftTransferFocal).restrict (P : Subgroup G)).ker =
      (P : Subgroup G).focalSubgroupOf := by
  letI : (P : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite
  change (((P : Subgroup G).transferFocal).restrict (P : Subgroup G)).ker =
    (P : Subgroup G).focalSubgroupOf
  exact ker_restrict_transferFocal_eq_focalSubgroupOf (P := P)

omit [Finite (Sylow p G)] in
public lemma ker_ftTransferFocal_inf_eq_focalSubgroup (P : Sylow p G) :
    ((P : Subgroup G).ftTransferFocal).ker ⊓ (P : Subgroup G) =
      (P : Subgroup G).focalSubgroup := by
  letI : (P : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite
  change ((P : Subgroup G).transferFocal).ker ⊓ (P : Subgroup G) =
    (P : Subgroup G).focalSubgroup
  exact ker_transferFocal_inf_eq_focalSubgroup (P := P)

end Subgroup

/-
**Kind**: Theorem
**Note**: Theorem 1.17
**Stmt**:
Let `G` be a finite group.
Let `p` be a prime.
Let `S` be a Sylow `p`-subgroup of `G`.
Then
`S ∩ G' = ⟨ x⁻¹ y | x, y ∈ S and x is conjugate to y in G ⟩`.
-/

public theorem theorem_1_17 {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (S : Sylow p G) :
    ((S : Subgroup G) ⊓ derivedSubgroup G) =
      Subgroup.closure {z : G | ∃ x : G, x ∈ (S : Subgroup G) ∧ ∃ y : G, y ∈ (S : Subgroup G) ∧
        IsConj x y ∧ z = x⁻¹ * y} := by
  simpa using sylow_inf_derivedSubgroup_eq_focalSubgroup (G := G) p S
