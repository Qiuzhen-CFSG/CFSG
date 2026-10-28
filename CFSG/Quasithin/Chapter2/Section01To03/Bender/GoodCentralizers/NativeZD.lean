module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.GoodCentralizers.ZD
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.BadCentralizers.Source115
public import CFSG.Quasithin.ClassificationModels
public import BenderSuzuki.ZD.Recognition.NativeSource

/-!
# The proved ZD theorem in the empty-delta branch

Theorem ZD, ordinary component balance and the complete marked quasisimple
involution classifier supply the three independent source inputs of the
good-centralizer argument. Its original Sylow subgroup, unique maximal
two-local subgroup and local-control witness retain all their markings.
Only the earlier universal A/B/C theorem for the full known-simple catalogue
remains explicit; its producer is `qt-a02-abc-assembly`.

Source: Aschbacher--Smith, Proposition 2.2.2 and the empty-delta case of
Theorem 2.1.1, printed pp.518--520.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.Section02
namespace CFSG.Quasithin.Chapter2.BenderFusion
universe u

/-- The simple ZD corollary, with the full finite-group theorem supplied. -/
theorem GoodCentralizers.simpleCorollaryZD :
    GoodCentralizers.SimpleCorollaryZD.{u} :=
  GoodCentralizers.simpleCorollaryZD_of_theoremZD BenderSuzuki.ZD.theorem_ZD

/-- The full marked empty-delta conclusion with ZD, ordinary balance and
the local component-action classifier discharged. -/
theorem source_marked_bender_of_delta_empty_and_theoremsABC
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC KnownSimple.IsKnownSimple X)
    (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅) :
    ∃ w : LocalControlWitness T M,
      IsProductDisconnected (involutionConjugates w.U) M ∧
      BenderSuzuki.IsBorelSubgroup M ∧ ClassificationModels.IsBenderModel G ∧
      M = normalizer (T : Set G) ∧
      ∃ n : ℕ, 2 ≤ n ∧ BenderSuzuki.IsSimpleBenderGroupAtExponent n G ∧
        w.U = omegaOneAmbient (T : Subgroup G) ∧
        w.U = (center T).map (T : Subgroup G).subtype ∧ Nat.card w.U = 2 ^ n :=
  source_marked_bender_of_delta_empty hG T M hM hTM hunique hdelta
    (BadCentralizers.componentSource115 hG hABC)
    BadCentralizers.ordinaryBalance13_knownSimple GoodCentralizers.simpleCorollaryZD

/-- The empty-delta case feeds the literal model conclusion of 2.1.1,
retaining only its independently proved earlier A/B/C source theorem. -/
theorem theorem_2_1_1_of_delta_empty_and_theoremsABC
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC KnownSimple.IsKnownSimple X)
    (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅) :
    ClassificationModels.IsTheorem211Model G := by
  obtain ⟨w, hw, hBorel, hBender, hrest⟩ :=
    source_marked_bender_of_delta_empty_and_theoremsABC hG hABC T M hM hTM hunique hdelta
  exact .bender hBender

end CFSG.Quasithin.Chapter2.BenderFusion
