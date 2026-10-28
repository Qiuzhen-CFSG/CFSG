module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Basic
public import Theory.ElementaryAbelian.Extraspecial

/-!+# The odd-primary intermediate configuration in 13.8.13

This contract separates supercritical construction from the three-primary
exclusions. Its Frattini interval and normality refer to the actual image
in H/O₂(H). The alternatives specify actual elementary or extraspecial
groups, including the exponent-p convention for p^(1+2).

No existence or exclusion is asserted here. The construction must prove
these fields from the standing setup; the three-primary case analyses may
take this intermediate configuration explicitly. Final assembly remains
responsible for constructing the existing `ReducedFive` contract.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.1.22–24
and the proof of 13.8.13, printed pp.25 and 950–951.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three
open Subgroup

/-- The three small odd-group alternatives, including the exponent condition. -/
def SmallOddGroup (p : ℕ) (P : Type*) [Group P] : Prop :=
  Nat.card P = p ∨
    (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
    (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ ∀ x : P, x ^ p = 1)

variable {G : Type*} [Group G]

/-- An intermediate output to be constructed, not an earlier-source hypothesis.
The small-group alternatives concern P* itself, not an unrelated carrier. -/
structure ReducedOdd (p : ℕ) (H L₁ T M Vα : Subgroup G) where
  prime : p.Prime
  odd : Odd p
  P : Subgroup G
  P_le : P ≤ H
  P_isPGroup : IsPGroup p P
  Pstar_small : SmallOddGroup p (Source.starImage H P)
  Pstar_normal : (Source.starImage H P).Normal
  moved : ⁅Source.starImage H P, Source.starImage H Vα⁆ ≠ ⊥
  outside : ¬ P ≤ M
  generated : H = P ⊔ (L₁ ⊔ T)
  irreducible : starFrattiniIrreducible H P L₁ T

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three
end
