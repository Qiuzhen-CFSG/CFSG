module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Centralizer
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalPairedPrime
/-!
# Proposition E.6.27 over the complete known-simple catalogue

The original higher-Thompson hypotheses construct the prescribed Sylow and
its normalizer bound. The proved numerical SQTK E.6.26 handles small minimal
parabolics. Actual component selection, sharp paired-prime generation and
the reflected Hall-Cartan construction handle every large parabolic, using
the same odd subgroup throughout. This discharges both earlier callbacks
while preserving precisely the four hypotheses of E.6.27.

Source: Aschbacher–Smith Proposition E.6.27, printed p.257.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
open ChapterB ParabolicCartan ParabolicCartan.MarkedModels
universe u
variable {G : Type u} [Group G] [Finite G]
theorem source_proposition_E_6_27
    {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (hn : nPrime (inducedAutomizer V (M ⊓ centralizer (U : Set G))) ≤ j)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤ M ⊓ centralizer (V : Set G))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ M ⊓ centralizer (V : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ M) :
    centralizer (U : Set G) ≤ M := by
  apply centralizer_le_of_paired_odd_generation ?_ h hU hUV hj1 hj hn hJ hodd
  intro H _ _ hH S hP hs K hK hgen hN p hp _ h7 hm
  let : Fact p.Prime := ⟨hp⟩
  exact paired_prime_isEGenerated_one ChapterA.Section02.theoremA_knownSimple
    hH S hP hs K hK hgen hN (by omega) hm
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
