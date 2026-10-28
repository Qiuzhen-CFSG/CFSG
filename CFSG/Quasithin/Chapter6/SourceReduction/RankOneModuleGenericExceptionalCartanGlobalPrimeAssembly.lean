module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLocal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeTerminal

/-!
# Assembly contracts for the prime-actor exclusion

The choice of the source rank-one factor, exclusion of the zero-core
amalgam models, and the changed-Sylow component argument are independent
source obligations. The last two can work with the explicit structural
output of the first. These predicates assert no inhabitants.

The assembly below verifies genuine F.1.1 on the literal (DS,L₂) pair
in the zero-core branch. In the other branch it feeds the original B
and D to the proved elementary order-twenty-seven contradiction in
N_G(L). It retains all three source obligations explicitly and therefore
does not claim to prove original 5.2.2 until they have been discharged.

Source: Aschbacher--Smith, 5.2.2, printed pp.647--649, with 5.1.10--13
on pp.634--638 (`refs/quasithin.pdf`).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The pre-normalization source choice and small-local analysis on pp.646--647.
The output has no assumption that D or the full Cartan normalizes L₂. -/
def SourceLocalConstruction (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
    Input KnownSimple.IsKnownSimple T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        CartanLocalControl A H → (n = 2 ∨ n = 4 ∨ n = 8) →
        ∀ (p : ℕ) (D : Subgroup G), CartanPrimeActor A H p D →
          ∃ L₂ : Subgroup G, LocalData T L H B D L₂

/-- The actual F.1.12 model exclusions on pp.647--648. Both the structural
selection and genuine F.1.1 are explicit, so this argument can be developed
independently of the source construction. -/
def SourceZeroCoreExclusion (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
    Input KnownSimple.IsKnownSimple T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        CartanLocalControl A H → (n = 2 ∨ n = 4 ∨ n = 8) →
        ∀ (p : ℕ) (D : Subgroup G), CartanPrimeActor A H p D →
          ∀ L₂ : Subgroup G, LocalData T L H B D L₂ →
            ChapterF.Source.HypothesisF11
              ![D ⊔ Global.sourceS L H, L₂] (Global.sourceS L H) → False

/-- The changed-Sylow and component-embedding conclusion on p.648.
It must construct the actual plane B and show that the same D moves L₂.
The final elementary rank contradiction is proved separately. -/
def SourceChangedSylow (G : Type u) [Group G] [Finite G] : Prop :=
  SourceLocalCartanEscape KnownSimple.IsKnownSimple G →
    ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
      Input KnownSimple.IsKnownSimple T L W n →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        1 < ChapterE.generationParameter H →
        ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
        ∀ A B : Subgroup G, CartanPair T L H A B →
          CartanLocalControl A H → (n = 2 ∨ n = 4 ∨ n = 8) →
          ∀ (p : ℕ) (D : Subgroup G), CartanPrimeActor A H p D →
            ∀ L₂ : Subgroup G, LocalData T L H B D L₂ →
              (generated L H D L₂).pCoreIn 2 ≠ ⊥ →
                p = 3 ∧ IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
                  ¬ D ≤ normalizer (L₂ : Set G)

/-- Conditional final assembly on the unchanged public prime-exclusion target.
Every extra source premise is displayed and remains to be discharged. -/
theorem sourceCartanPrimeExclusion_of_sources
    (hlocal : SourceLocalConstruction G)
    (hzero : SourceZeroCoreExclusion G) (hchanged : SourceChangedSylow G) :
    SourceCartanPrimeExclusion KnownSimple.IsKnownSimple G := by
  intro h513 T L W n h H hH hgen hthree A B c hcontrol hn p D hd
  obtain ⟨L₂, d⟩ := hlocal T L W n h H hH hgen hthree A B c hcontrol hn p D hd
  by_cases hz : (generated L H D L₂).pCoreIn 2 = ⊥
  · exact hzero T L W n h H hH hgen hthree A B c hcontrol hn p D hd L₂ d
      (d.hypothesisF11 h hH c hd hz)
  · obtain ⟨hp, hBe, hBcard, hD⟩ :=
      hchanged h513 T L W n h H hH hgen hthree A B c hcontrol hn p D hd L₂ d hz
    subst p
    exact h.prime_actor_excluded_of_cubic_plane c hd hBe hBcard d.B_normalizes_right hD

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
