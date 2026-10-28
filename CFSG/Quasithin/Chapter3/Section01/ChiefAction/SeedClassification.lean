module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SeedAction
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SingleBorel
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.PairedBorel
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallThompson

/-!
# Small natural alternatives on the essential source action

The essential quotient has a nonzero vector fixed by every original element
centralizing the distinguished module. The source residual-centralizer hypothesis
therefore excludes higher-field natural coordinates, using the single and paired
Borel lemmas. The remaining faithful action is a small natural wreath action or
a marked single or paired symmetric-five action.

This is the essential-factor step in the proof of original 3.1.9(5), used by
original 15.1.12(3). The sharp-offender transfer supplies its FF-module premise.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction

def ChiefSmallNaturalAlternatives {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W) : Prop :=
  SmallNaturalWreathAction ρ ∨ ChiefFiveMarkedSection ρ ∨
    ∃ d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype),
      Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
end CFSG.Quasithin.ChapterB

namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction Theory.GroupTheory
universe u
variable {G D W : Type u} [Group G] [Finite G] [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.small_natural_alternatives_of_fixed_seed
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G))
    (q : H →* D) (hq : Function.Surjective q) (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (hff : IsFFModule ρ) (v : W) (hvne : v ≠ 0)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v) :
    ChiefSmallNaturalAlternatives ρ := by
  let S := T.subtype h.right_mem.1.1.2
  have hD := sqtk_of_mem_H hG h.right_mem.1.1.1
  have hp := (minimalParabolic_reduced_image S hP q hq hc hn).2
  let := hi
  by_cases hs : Group.IsSolvable D
  · obtain ⟨d,ht,hstable,hr,hgen⟩ := source_solvable_minimalParabolic_factors
      (S.mapSurjective hq) hp hs hc hf hff
    have hcount := d.toSolvableFFFactors.count_eq_one_or_two_of_surjective_threeRank
      q hq (hD.stronglyQuasithin 3 (by decide) (by decide))
    exact Or.inl ((d.toSolvableFFFactors.small_natural_moved_action hf hc hr hcount
      (fun i j => let ⟨t,ht⟩ := ht i j; ⟨t,ht⟩)).wreath)
  · let c : SQTKQuotient KnownSimple.IsKnownSimple D := {
      Cover := H
      kernel := q.ker
      sqtk := hD
      equiv := QuotientGroup.quotientKerEquivOfSurjective q hq }
    rcases nonsolvable_offender_natural_source ρ
      (S.mapSurjective hq) hp hs hf hff hc ⟨c⟩
      with hqs | ⟨d,hd₁,hd₂⟩
    · obtain ⟨hqs,c,hlin | hsym⟩ := hqs
      · obtain ⟨F,⟨e⟩⟩ := hlin
        exact (h.quasisimple_natural_seed_impossible hP hres
          q hq hc hn
          ρ hf inferInstance v hvne
          hv hqs c.sectionData F e).elim
      · exact Or.inr (Or.inl ⟨hqs,c,hsym⟩)
    · obtain ⟨t,ht₁,ht₂,hmodel⟩ := source_offender_two_factor_shared_natural ρ
        (S.mapSurjective hq) hp hff hc d
      rcases hmodel with ⟨F,⟨e⟩⟩ | hsym
      · have hdeg := h.paired_natural_field_degree_eq_one hP hres
          q hq hc hn
          ρ hf inferInstance v hvne
          hv d F e
        exact (hs (source_pair_degree_one_solvable ρ
          (S.mapSurjective hq) hp hff hc d F hdeg e)).elim
      · exact Or.inr (Or.inr ⟨d,hsym⟩)

variable [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]

theorem EssentialSeedAction.small_natural_alternatives
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G))
    {hVH : V ≤ H} (a : EssentialSeedAction H V (T.subtype h.right_mem.1.1.2) hVH)
    (hff : IsFFModule a.imageRepresentation) : ChiefSmallNaturalAlternatives a.imageRepresentation := by
  let := a.irreducible
  exact h.small_natural_alternatives_of_fixed_seed hG a.original_minimal hres
    a.projection a.projection_surjective a.twoCore_eq_bot a.projection_kernel_ne_top
    a.imageRepresentation (imageRepresentation_injective a.representation)
    (imageRepresentation_irreducible a.representation a.irreducible) hff
    a.vector a.vector_ne_zero a.vector_centralizer_fixed
end CFSG.Quasithin.Chapter3
