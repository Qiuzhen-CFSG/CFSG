module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.GoodCentralizers
public import BenderSuzuki.ZD.SimpleCorollary

/-!
# Theorem ZD in the good-centralizer branch

The full product-disconnected theorem supplies precisely the simple model
and Borel corollary used by Proposition 2.2.2. Applying the proved local
construction preserves the original M, T and U, including the field exponent
and both Sylow markings. The parent still supplies Theorem ZD, 1.1.5 and the
ordinary balance theorem as genuine earlier-source implications.

Source: Aschbacher--Smith, Proposition 2.2.2, printed pp.519--520; GLS,
Volume 4, Chapter 2, Corollary ZD.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter2.BenderFusion
universe u

/-- Full Theorem ZD supplies the exact simple corollary required by the
already proved good-centralizer construction. -/
theorem GoodCentralizers.simpleCorollaryZD_of_theoremZD
    (sourceZD : ∀ {H : Type u} [Group H] [Finite H] (Z : Set H) (N : Subgroup H),
      IsProductDisconnected Z N → BenderSuzuki.ZD.Conclusion Z N) :
    GoodCentralizers.SimpleCorollaryZD.{u} := by
  intro G _ _ Z M hs hna h
  exact BenderSuzuki.ZD.simple_bender_borel_of_conclusion Z M h hs hna (sourceZD Z M h)

/-- The actual empty-delta source application, with the ZD corollary
and all original subgroup markings discharged from full Theorem ZD. -/
theorem source_marked_bender_of_delta_empty_of_theoremZD
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅)
    (source115 : BadCentralizers.ComponentSource115 G)
    (source13 : BadCentralizers.OrdinaryBalance13.{u} CFSG.KnownSimple.IsKnownSimple)
    (sourceZD : ∀ {H : Type u} [Group H] [Finite H] (Z : Set H) (N : Subgroup H),
      IsProductDisconnected Z N → BenderSuzuki.ZD.Conclusion Z N) :
    ∃ w : LocalControlWitness T M,
      IsProductDisconnected (involutionConjugates w.U) M ∧
      BenderSuzuki.IsBorelSubgroup M ∧ ClassificationModels.IsBenderModel G ∧
      M = normalizer (T : Set G) ∧
      ∃ n : ℕ, 2 ≤ n ∧ BenderSuzuki.IsSimpleBenderGroupAtExponent n G ∧
        w.U = omegaOneAmbient (T : Subgroup G) ∧
        w.U = (center T).map (T : Subgroup G).subtype ∧ Nat.card w.U = 2 ^ n := by
  exact source_marked_bender_of_delta_empty hG T M hM hTM hunique hdelta source115 source13
    (GoodCentralizers.simpleCorollaryZD_of_theoremZD sourceZD)

end CFSG.Quasithin.Chapter2.BenderFusion
