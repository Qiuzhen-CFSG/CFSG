module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LowRank
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.UnitaryThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CatalogueExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinaryRee
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Excluding the complete shared Theorem C catalogue

The actual residual placement theorem combines with the low-rank and
binary-unitary exclusions to close every Theorem C row of the selected
normal component. The dispatcher retains actual field equivalences, the
small derived groups, the entire component center, and its trivial two-core.

This is a branch exclusion for 4.4.3. B-only component rows and original
module fixation still require proof in the source Hall-faithfulness assembly.
Source: Aschbacher--Smith A.2.3--4 and 4.4.10--12, printed pp.33,621--623,
applied in 10.2.3(2), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
  (hu : UniqueMaximalOvergroup
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
  (K : Subgroup (normalizer (B : Set G)))
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
include D hn hBC hodd hBV hu hK hout

/-- Every shared Theorem C component row is excluded. The original residual,
full moved module, relative normality and complete center are retained. -/
theorem source_nonnormal_oddNormalizer_no_theoremC_component
    (hc : pCore 2 K = ⊥)
    (hm : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)) : False := by
  have hFK := source_nonnormal_oddNormalizer_residual_le_of_theoremC
    D hn B hBC hodd hBV hu K hK hout hm
  cases hm with
  | alternating n hn9 e =>
    exact source_nonnormal_oddNormalizer_no_placed_alternating_component
      D hn B hBC hodd hBV K hFK (by omega) e.some
  | odd hm =>
    have hlo := source_nonnormal_oddNormalizer_quotient_twoRank_ge_three
      D hn B hBC hodd hBV K hFK
    have hup := hm.twoRank_le_two
    omega
  | bender hm =>
    cases hm with
    | linear f hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact source_nonnormal_oddNormalizer_no_placed_binary_sl2_component
        D hn B hBC hodd hBV K hFK
        (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
    | unitary f hf hm =>
      exact source_nonnormal_oddNormalizer_no_placed_binary_unitary_three_component
        D hn B hBC hodd hBV K hFK (by omega) hm
    | suzuki m hm e =>
      exact source_nonnormal_oddNormalizer_no_placed_suzuki_component
        D hn B hBC hodd hBV K hFK (by omega) e.some
  | rank_two f hm =>
    cases hm with
    | linear hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact source_nonnormal_oddNormalizer_no_placed_psl3_component
        D hn B hBC hodd hBV K hFK e
    | symplectic hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact source_nonnormal_oddNormalizer_no_placed_sp4_component
        D hn B hBC hodd hBV K hFK
        (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
    | g2 hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      have hlarge : 2 < Nat.card F := by
        rw [hF]
        exact lt_of_lt_of_le (by decide : 2 < 2^2)
          (Nat.pow_le_pow_right (by decide) hf)
      exact source_nonnormal_oddNormalizer_no_placed_g2_component
        D hn B hBC hodd hBV K hFK hlarge e
    | triality hf hm =>
      obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f (by omega)).mp hm
      exact source_nonnormal_oddNormalizer_no_placed_triality_component
        D hn B hBC hodd hBV K hFK f (by omega) e
    | ree_f4 m hm _ e =>
      exact source_nonnormal_oddNormalizer_no_placed_ree_component
        D hn B hBC hodd hBV K hFK hm e.some
    | symplectic_derived _ e =>
      exact source_nonnormal_oddNormalizer_no_placed_alternating_component
        D hn B hBC hodd hBV K hFK (by decide : 6 ≤ 9)
        (e.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
    | g2_derived _ e =>
      exact source_nonnormal_oddNormalizer_no_placed_g2_derived_component
        D hn B hBC hodd hBV K hFK e.some
    | tits _ e =>
      exact source_nonnormal_oddNormalizer_no_placed_tits_component
        D hn B hBC hodd hBV K hFK e.some
  | linear_binary n hn45 hm =>
    exact source_nonnormal_oddNormalizer_no_placed_binary_linear_component
      D hn B hBC hodd hBV K hFK hn45 hm
  | sporadic hm =>
    exact source_nonnormal_oddNormalizer_no_shared_sporadic_component
      D hn B hBC hodd hBV hu K hK hout hc hm

end CFSG.Quasithin.Chapter10
