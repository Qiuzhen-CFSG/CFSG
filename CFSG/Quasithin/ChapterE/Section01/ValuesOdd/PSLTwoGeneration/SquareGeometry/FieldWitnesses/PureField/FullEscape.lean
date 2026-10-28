module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.FieldCentralizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.SmallField

/-!
# Local calculations and assembly for the full quadratic semilinear model

The descendants prove marked projective descent, the full field-involution
centralizer and its mixed-actor centralizers, literal ambient tau formulas,
and the intrinsic S₃ section when the fixed field has order three.

The final escape theorem is still an assembly obligation. The conditional
reduction below separates families containing a rank-two actor from families
whose nontrivial actors all have rank three. Both branches keep the original
family and its weak-closure normalizer; replacing it by a rank-selected
subfamily would require an additional normalizer argument. It uses the actual
top subgroup and transports the result through `Subgroup.topEquiv`.

Neither branch's escaping witness is assumed to come from only S₄ or
dihedral subgroups. All intrinsic E1/E2 conditions and the literal Sylow
intersection remain part of the branch obligations.

Source: Aschbacher–Smith, A.2.3(2), E.1.2 and E.1.14(6), printed pp.33,
209–210 and 214; the last cites Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape
variable {F : Type*} [Field F] [Finite F]

/-- Conditional assembly of the two remaining family branches. Both
hypotheses are matrix-local witness obligations, not conclusions proved here.
Rank-two families may contain rank-three actors as well. -/
theorem largeFamilyEscape_of_rank_branches {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) [Finite (PGammaL2 F)]
    (htwo : ∀ (T : Sylow 2 (⊤ : Subgroup (PGammaL2 F)))
      (Ω : Set (Subgroup (⊤ : Subgroup (PGammaL2 F)))), IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ →
        Group.rank A = 2 ∨ Group.rank A = 3) →
      (∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ Group.rank A = 2) →
      ∀ M : Subgroup (⊤ : Subgroup (PGammaL2 F)), IsCoatom M →
        (T : Subgroup _) ≤ M → normalizer (weakClosure (T : Subgroup _) Ω : Set _) ≤ M →
        ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧
          ∃ H, IsEMemberAt 1 (T : Subgroup _) A H ∧ ¬ H ≤ M)
    (hthree : ∀ (T : Sylow 2 (⊤ : Subgroup (PGammaL2 F)))
      (Ω : Set (Subgroup (⊤ : Subgroup (PGammaL2 F)))), IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ → Group.rank A = 3) →
      ∀ M : Subgroup (⊤ : Subgroup (PGammaL2 F)), IsCoatom M →
        (T : Subgroup _) ≤ M → normalizer (weakClosure (T : Subgroup _) Ω : Set _) ≤ M →
        ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧
          ∃ H, IsEMemberAt 1 (T : Subgroup _) A H ∧ ¬ H ≤ M) :
    ∀ T : Sylow 2 (PGammaL2 F), LargeFamilyEscapeAt T := by
  apply largeFamilyEscape_of_equiv (Subgroup.topEquiv :
    (⊤ : Subgroup (PGammaL2 F)) ≃* PGammaL2 F)
  intro T
  apply largeFamilyEscapeAt_of_rank_two_or_three_witnesses hp hodd hF _ T
  intro Ω hΩ hr M hM hTM hNM
  by_cases htwoActor : ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ Group.rank A = 2
  · exact htwo T Ω hΩ hr htwoActor M hM hTM hNM
  · apply hthree T Ω hΩ _ M hM hTM hNM
    intro A hA hAT hne
    exact (hr A hA hAT hne).resolve_left (fun ha => htwoActor ⟨A, hA, hAT, ha⟩)


end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape
