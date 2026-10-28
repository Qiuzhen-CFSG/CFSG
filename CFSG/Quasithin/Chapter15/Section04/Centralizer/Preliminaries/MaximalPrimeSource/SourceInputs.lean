module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.Preimages
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import CFSG.Quasithin.Chapter1.Section03.Terminal.Definitions
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.KnownSimple.CarrierCatalogue
public import Stellmacher.SectionsOneToFourDefs

/-!
# Literal earlier-source inputs for the maximal-prime argument

The propositions below are theorem parameters, not assertions of the earlier
results. They retain Hypothesis 15.4.1, all of 15.4.2(1–3), and both conclusions
of C.2.6. The C.2.6 product is an ordered setwise product, and each block is
subnormal relative to H and carries the actual alternating quotient and module.

Source: Aschbacher–Smith, combined manuscript, printed pp.1155–1157,
Definition 3.2.12 on p.584, Hypothesis C.2.3 on p.144 and C.2.6 on p.145.
The source discharge belongs to qt-15-04-prime-reduction and
qt-c-02-basic-pushing; no instance of these propositions is asserted here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Genuine 15.4.1 on the actual Sylow subgroup and its ambient central omega. -/
structure SourceHypotheses (T : Sylow 2 G) : Prop where
  simpleQTKE : IsSimpleQTKE KnownSimple.IsKnownSimple G
  empty_faithful : MainForward.faithfulLocalComponents T = ∅
  centralizer_overgroups : ∃ M₁ M₂ : Subgroup G,
    IsMaximalTwoLocal M₁ ∧ IsMaximalTwoLocal M₂ ∧
    centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M₁ ∧
    centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M₂ ∧ M₁ ≠ M₂

/-- Aut_G(X/O₂(X)), obtained from the actual ambient normalizer action. -/
def quotientAutomorphisms (X : Subgroup G) : Subgroup (MulAut (Chapter1.XiQuotient X)) :=
  ((Subgroup.quotientAut (pCore 2 X)).comp X.normalizerMonoidHom).range

/-- Literal Definition 3.2.12. This leaf keeps the definition local to avoid
changing another owner's Chapter 3 interface. -/
def XiMinus (T : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ Chapter1.Xi G T ∧
    ((∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = 3) ∨
      (IsPGroup 5 (Chapter1.XiQuotient X) ∧
        ∀ q : ℕ, q.Prime → q ∣ Nat.card (quotientAutomorphisms X) → q = 2 ∨ q = 5))}

/-- The complement Ξ⁺ in the actual uppercase Ξ family. -/
def XiPlus (T : Subgroup G) : Set (Subgroup G) := Chapter1.Xi G T \ XiMinus T

/-- All clauses of the earlier 15.4.2(1–3), including those unused in the
opening prime comparison. Clause (4) belongs to the separate q-hat argument. -/
structure Earlier1542Conclusion (T : Sylow 2 G) : Prop where
  empty_local : Chapter1.L G (T : Subgroup G) = ∅
  solvable : ∀ M : Subgroup G, IsMaximalTwoLocal M →
    (T : Subgroup G) ≤ M → Group.IsSolvable M
  uppercase : ∀ X ∈ Chapter1.Xi G (T : Subgroup G),
    ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), X⁆ ≠ ⊥ ∧
    X ∈ Chapter1.XiStarF G (T : Subgroup G) ∧ X ∉ XiPlus (T : Subgroup G) ∧
    (IsPGroup 3 (Chapter1.XiQuotient X) ∨ IsPGroup 5 (Chapter1.XiQuotient X))

/-- The complete earlier-source implication, whose producer is the parent. -/
def Earlier1542 : Prop :=
  ∀ T : Sylow 2 G, SourceHypotheses T → Earlier1542Conclusion T

/-- Both parts of genuine C.2.6, universally over finite ambient groups.
The Fitting hypothesis and all subgroup coordinates are literal. -/
def EarlierC26 : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (H R M_H : Subgroup D),
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple H R M_H →
    (generalizedFitting (twoFittingPreimage H)).map (twoFittingPreimage H).subtype = H.pCoreIn 2 →
    Chapter1.IsSylowIn 2 R (twoFittingPreimage H ⊔ R) ∧
    (¬ twoFittingPreimage H ≤ M_H →
      ∃ (n : ℕ) (L : Fin n → Subgroup D),
        (∀ i, L i ≤ twoFittingPreimage H ∧ ¬ L i ≤ M_H ∧
          ChapterC.IsBlock ((L i).subgroupOf H) ∧ ChapterC.IsAlternatingBlock (L i) 3) ∧
        ∀ x : D, x ∈ twoFittingPreimage H ↔
          ∃ m ∈ M_H ⊓ twoFittingPreimage H,
            ∃ l : Fin n → D, (∀ i, l i ∈ L i) ∧ x = m * (List.ofFn l).prod)

/-- The outside-block consequence used in 15.4.3 is derived from the full
ordered-product theorem parameter. Relative block subnormality is retained. -/
theorem outside_block_of_earlierC26 (h26 : EarlierC26.{u})
    {H R M_H : Subgroup G}
    (hsetup : Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple H R M_H)
    (hf : (generalizedFitting (twoFittingPreimage H)).map (twoFittingPreimage H).subtype = H.pCoreIn 2)
    (hout : ¬ twoFittingPreimage H ≤ M_H) :
    ∃ L : Subgroup G, L ≤ twoFittingPreimage H ∧ ¬ L ≤ M_H ∧
      ChapterC.IsBlock (L.subgroupOf H) ∧ ChapterC.IsAlternatingBlock L 3 := by
  obtain ⟨n, L, hL, hprod⟩ := (h26 G H R M_H hsetup hf).2 hout
  by_cases hn : n = 0
  · subst n
    exfalso
    apply hout
    intro x hx
    obtain ⟨m, hm, l, _, he⟩ := (hprod x).mp hx
    have hxm : x = m := by simpa using he
    rw [hxm]
    exact hm.1
  · exact ⟨L ⟨0, Nat.pos_of_ne_zero hn⟩, hL ⟨0, Nat.pos_of_ne_zero hn⟩⟩
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
