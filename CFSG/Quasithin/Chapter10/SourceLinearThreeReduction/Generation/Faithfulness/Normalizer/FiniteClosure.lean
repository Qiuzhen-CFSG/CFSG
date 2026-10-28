module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.BinaryClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.FiniteExclusions

/-!
# Discharging placement for the finite shared model rows

The existing Theorem C outer-solvability proof applies to the actual binary
linear, small derived G₂ and Mathieu carriers. Together with the original
covering-uniqueness subgroup it places the unchanged residual in the normal
component. The proved order obstruction then excludes these rows.

Source: Aschbacher--Smith 4.4.10--12 and the subsequent inspection,
printed pp.621--623. Module fixation and covering uniqueness remain earlier
obligations of qt-d-10-nona5-hall-faithfulness.
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

/-- Every binary linear-four/five normal component is excluded with its
outer action and original residual placement discharged. -/
theorem source_nonnormal_oddNormalizer_no_binary_linear_component
    {n : ℕ} (hn45 : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) n 2) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_binary_linear_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.linear_binary n hn45 hm)) hn45 hm

/-- The small derived G₂ normal component is excluded after discharging
its outer action and the literal residual placement. -/
theorem source_nonnormal_oddNormalizer_no_g2_derived_component
    (e : K ⧸ center K ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_g2_derived_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.rank_two 1 (.g2_derived rfl ⟨e⟩))) e

/-- The actual M11 normal component is excluded, including outer action
and placement of the unchanged fixed residual. -/
theorem source_nonnormal_oddNormalizer_no_m11_component
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M11) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_m11_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.sporadic (Or.inl ⟨.m11, (by intro h; cases h), ⟨e⟩⟩))) e

/-- The actual M12 normal component is excluded, including outer action
and placement of the unchanged fixed residual. -/
theorem source_nonnormal_oddNormalizer_no_m12_component
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M12) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_m12_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.sporadic (Or.inl ⟨.m12, (by intro h; cases h), ⟨e⟩⟩))) e

/-- The actual M22 normal component is excluded, including outer action
and placement of the unchanged fixed residual. -/
theorem source_nonnormal_oddNormalizer_no_m22_component
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M22) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_m22_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.sporadic (Or.inl ⟨.m22, (by intro h; cases h), ⟨e⟩⟩))) e

/-- The actual M23 normal component is excluded, including outer action
and placement of the unchanged fixed residual. -/
theorem source_nonnormal_oddNormalizer_no_m23_component
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M23) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_m23_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.sporadic (Or.inl ⟨.m23, (by intro h; cases h), ⟨e⟩⟩))) e

/-- The actual M24 normal component is excluded, including outer action
and placement of the unchanged fixed residual. -/
theorem source_nonnormal_oddNormalizer_no_m24_component
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M24) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_m24_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.sporadic (Or.inl ⟨.m24, (by intro h; cases h), ⟨e⟩⟩))) e

end CFSG.Quasithin.Chapter10
