module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.Position
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FixedAction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.QuotientRanks

/-!
# The two local construction branches for outer PSL₃ actors

A proper weak-closure normalizer supplies a nontrivial original family member.
The actor has order four or eight, with inner intersection of order two or four.
In each case an original family member can be chosen to contain an inner
involution central in the fixed Sylow subgroup. The two local escape
constructions can consequently be carried out independently.

The theorem below assembles these two constructions conditionally. Both local
escape premises remain required: the action, positioning and rank calculations
alone do not prove the outer-family case of E.1.14(7).

Source: Aschbacher--Smith, E.1.1--5 and E.1.14(7), printed pp.209--210, 214;
A.2.3(2), p.33, and A.3.21(a), p.55. The source generation result refers to
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- Conditional assembly for the two positioned actor sizes. The premises must
still be proved using the source prime and strongly-quasithin hypotheses. -/
theorem familyEscapes_of_positioned_outer_cases {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω)
    (houter : ¬ HasInnerActor F T Ω) (M : Subgroup (graphExtension F)) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (hfour : ∀ A ∈ Ω, A ≤ (T : Subgroup _) → Nat.card A = 4 →
      Nat.card (A ⊓ innerPart F : Subgroup _) = 2 →
      ∀ z : graphExtension F, orderOf z = 2 → z ∈ innerPart F → z ∈ A →
        (T : Subgroup _) ≤ centralizer ({z} : Set _) → FamilyEscapes F T Ω M)
    (height : ∀ A ∈ Ω, A ≤ (T : Subgroup _) → Nat.card A = 8 →
      Nat.card (A ⊓ innerPart F : Subgroup _) = 4 →
      ∀ z : graphExtension F, orderOf z = 2 → z ∈ innerPart F → z ∈ A →
        (T : Subgroup _) ≤ centralizer ({z} : Set _) → FamilyEscapes F T Ω M) :
    FamilyEscapes F T Ω M := by
  obtain ⟨A, hA, hAT, _, hcases, _⟩ :=
    OuterFamilies.exists_large_outer_actor F hp ho hF T Ω hΩ hlarge houter M hM hN
  rcases hcases with ⟨hfourA, hinner⟩ | ⟨heightA, hinner⟩
  · obtain ⟨B, hB, hBT, hfourB, hinnerB, z, hz2, hzL, hzB, hTz⟩ :=
      OuterFamilies.exists_positioned_four_actor F ho hF T hΩ hA hfourA hinner
    exact hfour B hB hBT hfourB hinnerB z hz2 hzL hzB hTz
  · let := hΩ.1 A hA
    obtain ⟨z, hz2, hzL, hzA, hTz⟩ :=
      OuterFamilies.exists_central_inner_involution_of_eight F hp ho hF hAT heightA hinner
    exact height A hA hAT heightA hinner z hz2 hzL hzA hTz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
