module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoTwoAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartan

/-!
# The original chosen-module Hall--Janko cubic

The same normal container supplied by the local Cartan sieve contains the
whole residual because it contains the seed and its full Sylow orbit.
Apply the proved native J₂ action bound and the three-rank transfer to the
unchanged chosen module and both original Hall factors. The entire actual
intersection A ∩ C is an escaping cubic. Its literal quotient action has
the same order; no degree-two or residual-A₅ hypothesis is inserted.

The original-Sylow inverter, residual recognition in this row, exhaustive
component selection and binary-triality exclusion remain source obligations.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, pp.637,795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- On the same selected J₂ container, the original action and the full
original Cartan intersection are cubic, and the latter escapes O²(H). -/
theorem rankOne_local_cartan_janko_two_cubic
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    Nat.card ((A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C))) = 3 ∧
      Nat.card (A ⊓ C.map Y.subtype : Subgroup G) = 3 ∧
      ¬ A ⊓ C.map Y.subtype ≤ normalizer (residual H : Set G) := by
  have hi := a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  have hYn : Y ≤ normalizer (C.map Y.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective]
      using (inferInstance : C.Normal)
  have hRX : residual H ≤ C.map Y.subtype := by
    rw [←horbit]
    exact iSup_conjugates_le_of_le_normalizer _ _ _ hKC
      (hH.1.1.2.trans (hY.2.trans hYn))
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRX
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  exact ⟨LocalSieve.janko_two_action_card_three hi hH hgen c hY hescape C hRC hm,
    LocalSieve.janko_two_cartan_intersection hi hH hgen c hY hescape C hC hRC hm⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
