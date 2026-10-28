module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSevenAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalSevenResidual

/-!
# The original chosen-module seven-point cubic

Apply the quotient-action bound and cubic construction to the unchanged
whole chosen module. The seed and normal container are the ones supplied
by `rankOne_local_cartan_seed_seven_reduction`; both Hall conditions and
the literal normal quotient action are preserved. In the A7 row this
constructs the escaping cubic in the same component, without an extra
cubic-order or model-placement premise. Its original-Sylow inversion and
the remaining sieve branches are still required for the final witness.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.636--637,795,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The selected seven-point covering quotient has the literal cubic action. -/
theorem rankOne_local_cartan_seven_action_card_three
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : IsAlternating (C ⧸ pCore 2 C) 7 ∨ IsAlternatingCover (C ⧸ pCore 2 C) 7) :
    Nat.card ((A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C))) = 3 := by
  exact LocalSieve.alternating_seven_action_card_three
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hK hKT horbit hY hescape C hC hKC hm

/-- The same selected A7 component contains an actual escaping cubic of the
original left Cartan. No change of the chosen module or Sylow is made. -/
theorem rankOne_local_cartan_seven_escaping_cubic
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : IsAlternating (C ⧸ pCore 2 C) 7) :
    ∃ D : Subgroup G, D ≤ A ⊓ C.map Y.subtype ∧ Nat.card D = 3 ∧
      ¬ D ≤ normalizer (residual H : Set G) := by
  exact LocalSieve.alternating_seven_escaping_cubic
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
