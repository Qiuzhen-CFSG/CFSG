module

public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.Reduction
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.StandardRank

/-!
# Discharging the outer-image premise of the sharp PSL₃ actor bound

The proved two-rank bound for the standard outer image supplies the numerical
outer premise in the existing fixed-group reduction. The literal fixed-group
estimates and graph-field actor selection remain explicit; their assembly
owner must still discharge them to obtain the unconditional sharp bound.

Source: Aschbacher–Smith E.1.14(1), printed p.214, and G.9, printed p.356;
GLS3, Theorem 2.5.12 and §2.7.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3Even.OuterElementaryRank
open Matrix.PSL3.OuterSolvable

variable {F : Type*} [Field F] [Finite F]

/-- The sharp-rank reduction with its standard outer-image bound discharged.
Only the two fixed-group estimates and rank-two actor selection remain. -/
theorem rank_le_of_fixed_and_selection {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f)
    (hfixed : ∀ a : MulAut PSL(3,F), a ∈ standard F → a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup PSL(3,F) → primeRank 2 a.fixedSubgroup ≤ f)
    (hmixedFixed : ∀ a : MulAut PSL(3,F), IsGraphField a → a ^ 2 = 1 →
      primeRank 2 a.fixedSubgroup ≤ f - 1)
    (hselect : ∀ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 2 E →
      E ≤ standard F →
      primeRank 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))) = 2 →
      ∃ a ∈ E, IsGraphField a)
    (E : Subgroup (MulAut PSL(3,F))) (hE : IsElementaryAbelian 2 E)
    (hEO : ¬ E ≤ MulAut.innerSubgroup PSL(3,F)) : Group.rank E ≤ f + 1 :=
  rank_le_of_fixed_calculations hf hF
    (standardOuter_two_rank_le_of_two_power_card F hf hF) hfixed hmixedFixed hselect E hE hEO

end Matrix.PSL3Even.OuterElementaryRank
