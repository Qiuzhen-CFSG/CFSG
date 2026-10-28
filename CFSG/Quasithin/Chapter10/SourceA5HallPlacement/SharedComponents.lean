module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PlacedBinaryComponents
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PlacedFiniteComponents
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentNormalityComplete
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.PerfectActors

/-!
# Exclusion of all shared Theorem C rows for the actual Hall component

The actual selected component is normal by the completed nonnormal
inspection. For each shared Theorem C row, proved outer solvability puts
the original residual inside the component, using covering uniqueness and
the odd centralizer argument. The rank-eight obstruction and marked binary
local bounds then eliminate every row, including the finite exceptions.
No outer-action or placement premise remains in this shared-family theorem.

Source: Aschbacher--Smith4.4.10--12, printed pp.621--622, with A.2.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A placed residual excludes the entire Theorem C family on the literal
component quotient. -/
theorem source_a5_oddNormalizer_no_placed_theoremC_component
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
    (hm : IsTheoremCModel (K ⧸ center K)) : False := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have h8 := source_a5_oddNormalizer_component_centralQuotient_twoRank_ge_eight
    D e hn hp B hB hBC hBV hperm K hK houtK hFK
  have h5 := source_a5_oddNormalizer_component_quotient_fiveRank_ge_two_of_residual_le
    D e hn B hBC hodd hBV K hFK
  cases hm with
  | alternating n hn hm => exact no_small_alternating_of_twoRank_ge_eight h8 (by omega) hm
  | odd hm => have hh := hm.twoRank_le_two; omega
  | bender hm =>
    exact source_a5_oddNormalizer_no_placed_bender_component D e hn B hBC hodd hBV K hFK houtK hm
  | rank_two f hm =>
    exact source_a5_oddNormalizer_no_placed_theoremC_rankTwo_component D e hn B hBC hodd hBV K hFK hm
  | linear_binary n hn hm => exact no_binary_linear_of_twoRank_ge_eight h8 hn hm
  | sporadic hm =>
    exact no_j4_of_fiveRank_ge_two h5
      (theoremBSporadic_j4_of_twoRank_ge_eight h8 hm.toTheoremBSporadicModel)

/-- All shared Theorem C models are impossible for the actual selected
component, with residual placement and outer action fully discharged. -/
theorem source_a5_oddNormalizer_no_theoremC_component
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
    (hm : IsTheoremCModel (K ⧸ center K)) : False := by
  let : K.Normal := source_a5_oddNormalizer_component_normal
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    ChapterA.Section03.SourceComponents.TheoremBOuter.of_theoremC
      (Group.IsPerfect.not_isMulCommutative _) hm
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  have hi := source_oddNormalizer_component_inner B K hK hFK
  have hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))) := by
    intro y _
    exact le_normalizer_of_normal (mem_top y)
  obtain ⟨_,_,_,hF⟩ := source_a5_oddNormalizer_component_closure_of_overlap_normalizes
    D e hn hp B hB hBC hBV hperm K hK houtK hYK hi
  exact source_a5_oddNormalizer_no_placed_theoremC_component
    D e hn hp B hB hBC hBV hperm K hK houtK hF hm


/-- The additional alternating degree-nine row is excluded by the same
normal-component closure and the exact source rank-eight bound. -/
theorem source_a5_oddNormalizer_no_small_alternating_component
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
    {n : ℕ} (hnine : n ≤ 9)
    (hm : Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin n))) : False := by
  let : K.Normal := source_a5_oddNormalizer_component_normal
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    ChapterA.Section03.SourceComponents.TheoremBOuter.alternating
      (Group.IsPerfect.not_isMulCommutative _) hm
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  have hi := source_oddNormalizer_component_inner B K hK hFK
  have hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))) := by
    intro y _
    exact le_normalizer_of_normal (mem_top y)
  obtain ⟨_,_,_,hF⟩ := source_a5_oddNormalizer_component_closure_of_overlap_normalizes
    D e hn hp B hB hBC hBV hperm K hK houtK hYK hi
  exact no_small_alternating_of_twoRank_ge_eight
    (source_a5_oddNormalizer_component_centralQuotient_twoRank_ge_eight
      D e hn hp B hB hBC hBV hperm K hK houtK hF) hnine hm

/-- All odd PSL2 fields are excluded with outer action supplied by their
proved semilinear automorphism coverage. Component normality is unnecessary. -/
theorem source_oddNormalizer_no_odd_psl2_component_of_normalizes
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 q)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) : False := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    ChapterA.Section03.SourceComponents.TheoremBOuter.linear_two_odd
      (Group.IsPerfect.not_isMulCommutative _) ho hm
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  exact source_oddNormalizer_no_odd_psl2_component D B hBC hodd hBV K houtK
    (hF.symm ▸ ho) a (source_oddNormalizer_component_inner B K hK hFK)

end CFSG.Quasithin.Chapter10
