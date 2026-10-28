module

public import Theory.SpecificGroups.HigherLinear.ParabolicPlacement.Transport

/-!
# Assembly of higher-linear parabolic placement

Standard SL overgroup exhaustion gives a nonzero proper invariant subspace
for every proper overgroup of an arbitrary supplied projective Sylow. The
parabolic is proper in the actual quotient by the SL center, and its published
radical lies in that Sylow and therefore in the overgroup.

This module currently retains the standard-coordinate exhaustion premise.
The independent unitriangular Bruhat and root/cut proofs must discharge it
before the general placement theorem is complete. The radical centralizer
calculation is independent and is not used here.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, printed p.74 (PDF p.85),
the characteristic-two argument on pp.47–48, and GLS III, §2.6.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace Matrix.HigherLinear
open Theory.SpecificGroups.LinearSylowNormalizers

/-- The actual source consumer of standard SL placement, including properness
and containment of the published radical in the specified Sylow and overgroup.
The standard placement premise is still explicit. -/
theorem exists_proper_parabolic_and_radical_of_standard_overgroups
    {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n)
    (hstandard : ∀ H : Subgroup SL(n,F), unipotent n F ≤ H → H ≠ ⊤ →
      ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ H ≤ parabolicSL W)
    (S : Sylow 2 PSL(n,F)) (X : Subgroup PSL(n,F))
    (hSX : (S : Subgroup PSL(n,F)) ≤ X) (hX : X ≠ ⊤) :
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      X ≤ parabolic W ∧ parabolic W ≠ ⊤ ∧
      radical W ≤ (S : Subgroup PSL(n,F)) ∧ radical W ≤ X := by
  obtain ⟨W, hW, hWt, hXP⟩ :=
    exists_parabolic_of_standard_overgroups (by omega) hstandard S X hSX hX
  exact ⟨W, hW, hWt, hXP, parabolic_ne_top (by omega) hW hWt,
    radical_le_sylow_of_le_parabolic S W (hSX.trans hXP),
    radical_le_overgroup_of_le_parabolic S X W hSX hXP⟩

end Matrix.HigherLinear
