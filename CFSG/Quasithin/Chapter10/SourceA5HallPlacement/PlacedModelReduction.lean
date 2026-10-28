module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PlacedBinaryComponents
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PlacedUnitaryComponents
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PlacedFiniteComponents

/-!
# The remaining placed Hall component is an odd Theorem B model

All characteristic-two rank-two alternatives, including the B-only unitary
families, contradict the literal perfect local marking. Together with the
finite rank and rank-one exclusions, this leaves only the odd-characteristic
family for any actual component containing the original residual. Placement
remains with the independent normal-component action argument.

Source: Aschbacher--Smith4.4.12, printed pp.621--622, and A.2.2.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The full characteristic-two rank-two catalogue is excluded on the
literal placed residual, including PSU4 and PSU5. -/
theorem source_a5_oddNormalizer_no_placed_rankTwo_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {f : ℕ} (hm : IsRankTwoModel (K ⧸ center K) f) : False := by
  have hC (h : IsTheoremCRankTwoModel (K ⧸ center K) f) :=
    source_a5_oddNormalizer_no_placed_theoremC_rankTwo_component D e hn B hBC hodd hBV K hFK h
  cases hm with
  | linear hf hm => exact hC (.linear hf hm)
  | unitary_four hf hm =>
    exact source_a5_oddNormalizer_component_not_binary_unitary_four_of_residual_le
      D e hn B hBC hodd hBV K hFK hf hm
  | unitary_five hf hm =>
    subst f
    exact source_a5_oddNormalizer_component_not_unitary_five_four_of_residual_le
      D e hn B hBC hodd hBV K hFK hm
  | symplectic hf hm => exact hC (.symplectic hf hm)
  | g2 hf hm => exact hC (.g2 hf hm)
  | triality hf hm => exact hC (.triality hf hm)
  | ree_f4 m hm hf a => exact hC (.ree_f4 m hm hf a)
  | symplectic_derived hf hm => exact hC (.symplectic_derived hf hm)
  | g2_derived hf hm => exact hC (.g2_derived hf hm)
  | tits hf hm => exact hC (.tits hf hm)

/-- Once the original residual is placed, the complete Theorem B
inspection leaves only its odd-characteristic alternative. -/
theorem source_a5_oddNormalizer_placed_component_odd_model
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (hmodel : IsTheoremBModel (K ⧸ center K)) : IsTheoremBOddModel (K ⧸ center K) := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  rcases source_a5_oddNormalizer_component_infinite_theoremB_families
    D e hn hp B hB hBC hBV hperm K hK houtK hFK hmodel with ho | hb | ⟨f,hr⟩
  · exact ho
  · exact False.elim (source_a5_oddNormalizer_no_placed_bender_component
      D e hn B hBC hodd hBV K hFK houtK hb)
  · exact False.elim (source_a5_oddNormalizer_no_placed_rankTwo_component
      D e hn B hBC hodd hBV K hFK hr)

end CFSG.Quasithin.Chapter10
