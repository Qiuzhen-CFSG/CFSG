module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankThreeFamilies.InnerContainment
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankThreeFamilies.NormalTransfer

/-!
# Rank-three families in the full quadratic semilinear group

Every rank-three actor lies in the canonical normal inner extension
`PSL₂(F)⟨σ⟩`, and every ambient Sylow supplements that extension. Restricting
the entire family therefore preserves its weak closure under the subtype
map. Rank-three self-centralization gives ambient tau equal to the actor,
so an escaping inner-model E-member lifts through E.1.8, preserving every
intrinsic E1/E2 clause and the literal Sylow intersection.

The theorem below supplies exactly the hthree branch of
`FullEscape.largeFamilyEscape_of_rank_branches` once the independent
inner-model escape theorem is available. It does not assume that a chosen
standard actor belongs to the family or that the prime-field S₄/dihedral
list exhausts the semilinear local witnesses. Both small characteristics
and families without nontrivial members are retained.

The inner-model escape premise remains a genuine assembly obligation in the
independent `InnerEscape` development. This module does not yet establish the
unconditional hthree branch or the full-model theorem.

Source: Aschbacher--Smith, A.2.3(2), E.1.2, E.1.8 and E.1.14(6), printed
pp.33, 209--211 and 214; the final model calculation cites Asc82a, Lemma 4.10.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankThreeFamilies
variable {F : Type*} [Field F] [Finite F]

/-- Exact rank-three-family branch for the actual top subgroup, conditional
only on escape in the independent canonical inner model. -/
theorem escape_of_innerModel_escape {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) [Finite (PGammaL2 F)]
    (hescape : ∀ Q : Sylow 2 (innerModel F σ), LargeFamilyEscapeAt Q)
    (T : Sylow 2 (⊤ : Subgroup (PGammaL2 F)))
    (Ω : Set (Subgroup (⊤ : Subgroup (PGammaL2 F)))) (hΩ : IsElementaryFamily Ω)
    (hthree : ∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ → Group.rank A = 3)
    (M : Subgroup (⊤ : Subgroup (PGammaL2 F))) (hM : IsCoatom M)
    (hTM : (T : Subgroup _) ≤ M)
    (hNM : normalizer (weakClosure (T : Subgroup _) Ω : Set _) ≤ M) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧
      ∃ H, IsEMemberAt 1 (T : Subgroup _) A H ∧ ¬ H ≤ M := by
  let S : Subgroup (PGammaL2 F) := ⊤
  let N := (innerModel F σ).subgroupOf S
  let : (innerModel F σ).Normal := innerModel_normal hp hodd hF σ
  let : N.Normal := inferInstance
  have hescapeN : ∀ Q : Sylow 2 N, LargeFamilyEscapeAt Q :=
    largeFamilyEscape_of_equiv (subgroupOfEquivOfLe (show innerModel F σ ≤ S from le_top)).symm
      hescape
  have hgen : (T : Subgroup S) ⊔ N = ⊤ := by
    apply map_injective (f := S.subtype) S.subtype_injective
    rw [Subgroup.map_sup, show N.map S.subtype = innerModel F σ from
      map_subgroupOf_eq_of_le (show innerModel F σ ≤ S from le_top),
      map_top_of_surjective S.subtype Subgroup.topEquiv.surjective]
    exact sylow_sup_innerModel hp hodd hF σ
      (T.mapSurjective (f := S.subtype) (Subgroup.topEquiv.surjective))
  apply escape_of_normal_subgroup N T hgen hescapeN Ω hΩ ?_ ?_ ?_ M hTM hM.ne_top hNM
  · intro A hA hAT hneA
    rw [hthree A hA hAT hneA]
    decide
  · intro A hA hAT
    by_cases hbot : A = ⊥
    · exact hbot ▸ bot_le
    exact map_le_iff_le_comap.mp (rank_three_le_innerModel hp hodd hF σ hsq hne
      S le_top A (hΩ.1 A hA) (hthree A hA hAT hbot))
  · intro A hA hAT hneA
    exact tau_eq_of_rank_three hp hodd hF hlarge S le_top T A (hΩ.1 A hA) hAT
      (hthree A hA hAT hneA)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankThreeFamilies
