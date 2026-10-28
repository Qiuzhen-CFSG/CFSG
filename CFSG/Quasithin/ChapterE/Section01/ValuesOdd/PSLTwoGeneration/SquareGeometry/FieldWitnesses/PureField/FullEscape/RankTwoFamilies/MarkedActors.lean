module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.MarkedActors.Restriction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.MarkedActors.Centralizers
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape

/-!
# Escape for families containing marked mixed four-groups

If the original family has a linear four-group, use the independently owned
linear-placement branch. Otherwise all its nontrivial actors in the Sylow are
non-linear: the rank-three field projection excludes the only other possibility.
Their centralizers, hence their actual ambient taus, lie in the canonical normal
inner extension PSL₂(F)⟨σ⟩. Restrict the entire original family to that subgroup
and lift its escaping E-member using E.1.8. Its weak closure, normalizer and
literal Sylow intersections are retained throughout.

The unconditional theorem `escape` has the literal `hmarked` conclusion consumed by
`RankTwoFamilies.escape_of_linear_and_marked`. It permits a different escaping
actor, including one of rank three, and includes p=3 and p=5. This route does
not require every marked involution to have nontrivial image in the small-field
S₃ quotient, or restrict witnesses to S₄ and dihedral subgroups.

The final assembly applies `InnerEscape.escape` and `LinearActors.escape` to
discharge both premises of the conditional reduction. No generation, escape
or local-witness premise remains.

Source: Aschbacher--Smith, A.2.3(2), E.1.2, E.1.8 and E.1.14(6), printed
pp.33, 209--211 and 214; the last cites Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.MarkedActors
variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]

/-- If there is no linear four-group in the original family, all its
nontrivial actors and their actual ambient taus lie in the normal inner model.
Escape there lifts with the same family and weak closure. -/
theorem escape_of_no_linear_four {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hinner : ∀ Q : Sylow 2 (innerModel F σ), LargeFamilyEscapeAt Q)
    (T : Sylow 2 (PGammaL2 F)) (Ω : Set (Subgroup (PGammaL2 F)))
    (hΩ : IsElementaryFamily Ω)
    (hrange : ∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ →
      Group.rank A = 2 ∨ Group.rank A = 3)
    (hno : ¬ ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ Group.rank A = 2 ∧
      A ≤ pGammaL2PGLRange F)
    (M : Subgroup (PGammaL2 F)) (hTM : (T : Subgroup _) ≤ M) (hM : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup _) Ω : Set _) ≤ M) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧
      ∃ H, IsEMemberAt 1 (T : Subgroup _) A H ∧ ¬ H ≤ M := by
  have hnonlinear : ∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ →
      ¬ A ≤ pGammaL2PGLRange F := by
    intro A hA hAT hAb
    rcases hrange A hA hAT hAb with hr | hr
    · exact fun hL => hno ⟨A, hA, hAT, hr, hL⟩
    · exact rank_three_not_linear hp hodd hF σ hne A (hΩ.1 A hA) hr
  let : (innerModel F σ).Normal := RankThreeFamilies.innerModel_normal hp hodd hF σ
  apply escape_of_tau_le_normal_subgroup (innerModel F σ) T
    (RankThreeFamilies.sylow_sup_innerModel hp hodd hF σ T) hinner Ω hΩ
    ?_ ?_ ?_ M hTM hM hNM
  · intro A hA hAT hAb
    rcases hrange A hA hAT hAb with hr | hr <;> omega
  · intro A hA hAT
    by_cases hAb : A = ⊥
    · exact hAb ▸ bot_le
    let := hΩ.1 A hA
    exact (Subgroup.le_centralizer A).trans
      (centralizer_le_innerModel_of_not_linear hp hodd hF σ hsq hne A
        (hΩ.1 A hA) (hnonlinear A hA hAT hAb))
  · intro A hA hAT hAb
    exact tau_le_innerModel_of_not_linear hp hodd hF hlarge σ hsq hne
      (T : Subgroup _) A (hΩ.1 A hA) (hnonlinear A hA hAT hAb)

/-- The literal marked-family input of `RankTwoFamilies.escape_of_linear_and_marked`,
conditional on the two independently owned inner-model and linear-family branches.
The distinguished actor is allowed to change, including to rank three. -/
theorem marked_escape_of_inner_and_linear {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hinner : ∀ Q : Sylow 2 (innerModel F σ), LargeFamilyEscapeAt Q)
    (hlinear : ∀ (T : Sylow 2 (PGammaL2 F)) (Ω : Set (Subgroup (PGammaL2 F))),
      IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ → Group.rank A = 2 ∨ Group.rank A = 3) →
      (∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ Group.rank A = 2 ∧ A ≤ pGammaL2PGLRange F) →
      ∀ M : Subgroup (PGammaL2 F), IsCoatom M → (T : Subgroup _) ≤ M →
        normalizer (weakClosure (T : Subgroup _) Ω : Set _) ≤ M →
        ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ ∃ H, IsEMemberAt 1 (T : Subgroup _) A H ∧ ¬ H ≤ M) :
    ∀ (T : Sylow 2 (PGammaL2 F)) (Ω : Set (Subgroup (PGammaL2 F))),
      IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ → Group.rank A = 2 ∨ Group.rank A = 3) →
      ∀ b : PGL2 (FixedPoints.subfield (zpowers σ) F), orderOf b = 2 →
      (zpowers b).map (subfieldEmbedding σ) ⊔ zpowers (SemidirectProduct.inr σ) ∈ Ω →
      (zpowers b).map (subfieldEmbedding σ) ⊔ zpowers (SemidirectProduct.inr σ) ≤
        (T : Subgroup _) →
      ∀ M : Subgroup (PGammaL2 F), IsCoatom M → (T : Subgroup _) ≤ M →
        normalizer (weakClosure (T : Subgroup _) Ω : Set _) ≤ M →
        ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ ∃ H, IsEMemberAt 1 (T : Subgroup _) A H ∧ ¬ H ≤ M := by
  intro T Ω hΩ hrange _ _ _ _ M hM hTM hNM
  by_cases hL : ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ Group.rank A = 2 ∧ A ≤ pGammaL2PGLRange F
  · exact hlinear T Ω hΩ hrange hL M hM hTM hNM
  · exact escape_of_no_linear_four hp hodd hF hlarge σ hsq hne hinner
      T Ω hΩ hrange hL M hTM hM.ne_top hNM

/-- The literal marked-family input of `RankTwoFamilies.escape_of_linear_and_marked`,
with inner-model escape and linear placement discharged. This holds for every
marked involution of the fixed-field PGL₂, including p=3 and p=5. The escaping
actor remains in the original family and may differ from the marked four-group. -/
theorem escape {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) :
    ∀ (T : Sylow 2 (PGammaL2 F)) (Ω : Set (Subgroup (PGammaL2 F))),
      IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ → Group.rank A = 2 ∨ Group.rank A = 3) →
      ∀ b : PGL2 (FixedPoints.subfield (zpowers σ) F), orderOf b = 2 →
      (zpowers b).map (subfieldEmbedding σ) ⊔ zpowers (SemidirectProduct.inr σ) ∈ Ω →
      (zpowers b).map (subfieldEmbedding σ) ⊔ zpowers (SemidirectProduct.inr σ) ≤
        (T : Subgroup _) →
      ∀ M : Subgroup (PGammaL2 F), IsCoatom M → (T : Subgroup _) ≤ M →
        normalizer (weakClosure (T : Subgroup _) Ω : Set _) ≤ M →
        ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ ∃ H, IsEMemberAt 1 (T : Subgroup _) A H ∧ ¬ H ≤ M := by
  exact marked_escape_of_inner_and_linear hp hodd hF hlarge σ hsq hne
    (InnerEscape.escape hp hodd hF σ hsq hne) (LinearActors.escape hp hodd hF hlarge)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.MarkedActors
