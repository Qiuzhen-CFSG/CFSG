module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SharedComponents
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.FiniteInnerSymplectic

/-!
# The additional finite Theorem B components are impossible

The completed component-normality theorem and small-Frattini Sylow argument
supply inner action in the J3 and McL rows. Covering uniqueness then places
the original residual in K, contradicting the certified two-rank bounds.
The same closure applies to Sp6(2), where the marked five-rank is too large.
Together with the shared-family exclusion this removes the full thirteen-row
sporadic list and the remaining finite symplectic row, without a
residual-placement or outer-action callback.

Source: Aschbacher--Smith4.4.10--12, printed pp.621--622, and A.2.2.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The two B-only sporadic rows supply actual inner action and therefore
contradict the original rank-eight obstruction. -/
theorem source_a5_oddNormalizer_no_j3_or_mcl_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hm : Nonempty ((K ⧸ center K) ≃* Sporadic.Janko3.Model) ∨
      Nonempty ((K ⧸ center K) ≃* Sporadic.LeechRelated.McL.Carrier)) : False := by
  let : K.Normal := source_a5_oddNormalizer_component_normal
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  let : IsQuasisimple K := hK.2
  have hi := source_a5_oddNormalizer_inner_of_j3_or_mcl D e hn hp B hB hBC hperm K hm
  have hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))) := by
    intro y _
    exact le_normalizer_of_normal (mem_top y)
  obtain ⟨_,_,_,hF⟩ := source_a5_oddNormalizer_component_closure_of_overlap_normalizes
    D e hn hp B hB hBC hBV hperm K hK houtK hYK hi
  have h8 := source_a5_oddNormalizer_component_centralQuotient_twoRank_ge_eight
    D e hn hp B hB hBC hBV hperm K hK houtK hF
  rcases hm with ha | ha
  · obtain ⟨a⟩ := ha
    rw [primeRank_equiv 2 a] at h8
    have hu := Theory.SpecificGroups.FiniteModelTwoRank.j3_le_seven
    omega
  · obtain ⟨a⟩ := ha
    rw [primeRank_equiv 2 a] at h8
    have hu := Theory.SpecificGroups.FiniteModelTwoRank.mcl_le_seven
    omega

/-- All thirteen sporadic Theorem B models are excluded on the original
component, without assuming residual placement. -/
theorem source_a5_oddNormalizer_no_theoremB_sporadic_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hm : IsTheoremBSporadicModel (K ⧸ center K)) : False := by
  rcases hm with ⟨n,ha⟩ | ha | ha
  · by_cases h3 : n = .j3
    · subst n
      exact source_a5_oddNormalizer_no_j3_or_mcl_component
        D e hn hp B hne hB hBC hBV hperm K hK houtK hFK (Or.inl ha)
    · exact source_a5_oddNormalizer_no_theoremC_component
        D e hn hp B hne hB hBC hBV hperm K hK houtK hFK (.sporadic (Or.inl ⟨n,h3,ha⟩))
  · exact source_a5_oddNormalizer_no_theoremC_component
      D e hn hp B hne hB hBC hBV hperm K hK houtK hFK (.sporadic (Or.inr ha))
  · exact source_a5_oddNormalizer_no_j3_or_mcl_component
      D e hn hp B hne hB hBC hBV hperm K hK houtK hFK (Or.inr ha)

/-- The additional binary symplectic row has actual inner action; after
source closure its five-rank bound contradicts the literal residual marking. -/
theorem source_a5_oddNormalizer_no_binary_symplectic_six_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 3 2) : False := by
  let : K.Normal := source_a5_oddNormalizer_component_normal
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  let : IsQuasisimple K := hK.2
  have hi := source_a5_oddNormalizer_inner_of_binary_symplectic_six
    D e hn hp B hB hBC hperm K hm
  have hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))) := by
    intro y _
    exact le_normalizer_of_normal (mem_top y)
  obtain ⟨_, _, _, hF⟩ := source_a5_oddNormalizer_component_closure_of_overlap_normalizes
    D e hn hp B hB hBC hBV hperm K hK houtK hYK hi
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n, he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  exact (source_a5_oddNormalizer_component_no_j4_or_binary_symplectic_six_of_residual_le
    D e hn B hBC hodd hBV K hF).2 hm

/-- Before residual placement, the complete catalogue leaves precisely
the odd-characteristic models and the two additional binary unitary families. -/
theorem source_a5_oddNormalizer_component_odd_or_binary_unitary_model
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    IsTheoremBOddModel (K ⧸ center K) ∨
      (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ f)) ∨
      ClassicalGroup.IsPSU (K ⧸ center K) 5 4 := by
  have hC := source_a5_oddNormalizer_no_theoremC_component
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  cases source_oddNormalizer_component_theoremB D B hne K hK with
  | alternating n hbound hm =>
    exact (source_a5_oddNormalizer_no_small_alternating_component
      D e hn hp B hne hB hBC hBV hperm K hK houtK hFK hbound hm).elim
  | odd hm => exact Or.inl hm
  | bender hm => exact (hC (.bender hm)).elim
  | rank_two f hm =>
    cases hm with
    | linear hf hm => exact (hC (.rank_two f (.linear hf hm))).elim
    | unitary_four hf hm => exact Or.inr (Or.inl ⟨f, hf, hm⟩)
    | unitary_five hf hm =>
      subst f
      exact Or.inr (Or.inr hm)
    | symplectic hf hm => exact (hC (.rank_two f (.symplectic hf hm))).elim
    | g2 hf hm => exact (hC (.rank_two f (.g2 hf hm))).elim
    | triality hf hm => exact (hC (.rank_two f (.triality hf hm))).elim
    | ree_f4 m hm hf a => exact (hC (.rank_two f (.ree_f4 m hm hf a))).elim
    | symplectic_derived hf hm =>
      exact (hC (.rank_two f (.symplectic_derived hf hm))).elim
    | g2_derived hf hm => exact (hC (.rank_two f (.g2_derived hf hm))).elim
    | tits hf hm => exact (hC (.rank_two f (.tits hf hm))).elim
  | linear_binary n hn hm => exact (hC (.linear_binary n hn hm)).elim
  | symplectic_binary hm =>
    exact (source_a5_oddNormalizer_no_binary_symplectic_six_component
      D e hn hp B hne hB hBC hBV hperm K hK houtK hFK hm).elim
  | sporadic hm =>
    exact (source_a5_oddNormalizer_no_theoremB_sporadic_component
      D e hn hp B hne hB hBC hBV hperm K hK houtK hFK hm).elim

/-- The actual escaping normalizer has a normal component in one of the
three remaining families. No separate model, normality or placement premise
is imposed on the original odd actor. -/
theorem source_a5_oddPrimeNormalizer_remaining_normal_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (hout : ¬ normalizer (B : Set G) ≤ D.maximalLocal) :
    ∃ K : Subgroup (normalizer (B : Set G)),
      IsComponent (normalizer (B : Set G)) K ∧ K.Normal ∧
      ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal ∧
      ((solvableResidual
        (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
          (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
            (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))) ∧
      (IsTheoremBOddModel (K ⧸ center K) ∨
        (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ f)) ∨
        ClassicalGroup.IsPSU (K ⧸ center K) 5 4) := by
  obtain ⟨K, hK, _, houtK, _, _, _, hFK, _⟩ :=
    source_a5_oddPrimeNormalizer_moved_component D e hn hp B hne hB hBC hBV hperm hout
  exact ⟨K, hK, source_a5_oddNormalizer_component_normal
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK, houtK, hFK,
    source_a5_oddNormalizer_component_odd_or_binary_unitary_model
      D e hn hp B hne hB hBC hBV hperm K hK houtK hFK⟩

end CFSG.Quasithin.Chapter10

