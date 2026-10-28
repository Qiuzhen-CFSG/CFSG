module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.Theta
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LocalSubgroups
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ComponentNormality
public import CFSG.Quasithin.Chapter13.Section05.PointAction
public import Theory.GroupTheory.PrimeOrderClosure
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankAutomorphismOrder

/-!
# The seed normalizer and its rank-two theta subgroup

The genuine earlier centralizer statement13.5.4(4), through13.5.5, puts
N_H(V₃) in M. Thus its cubic closure lies in theta(H∩M)=L₁. For a normal
component K the cubic closure of N_K(V₃) is T-invariant. Its three-rank
is unchanged by cubic generation or by the local two-core quotient.
Rank two therefore fills the covered order-nine quotient. Two-perfect
lifting recovers the full subgroup L₁. The original component consumers
discharge component normality using13.7.5(1).

Source: Aschbacher–Smith,13.7.5(3),(4), printed p.938.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Original13.7.5(3), consuming the earlier13.5.4(4) centralizer statement. -/
theorem seed_normalizer_le_local
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G)) :
    H ⊓ normalizer (V₃ : Set G) ≤ M :=
  ((inf_le_inf_right _ hH.2.1).trans
    (Section05.PointAction.normalizer_intersection_source d hcentral)).trans inf_le_left

/-- Cubics in the seed normalizer lie in the original point residual. -/
theorem seed_normalizer_theta_le
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) :
    closure {x : G | x ∈ K ⊓ normalizer (V₃ : Set G) ∧ orderOf x = 3} ≤
      sourceOne L T V₁ := by
  rw [← theta_intersection d h hH]
  apply Subgroup.closure_mono
  rintro x ⟨hx, ho⟩
  exact ⟨⟨hKH hx.1, seed_normalizer_le_local d hH hcentral ⟨hKH hx.1, hx.2⟩⟩, ho⟩

/-- Rank two forces the covered local model and fills its actual point residual. -/
theorem covered_and_theta_of_normal_component_rank_two
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    (hrank : primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 2) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      closure {x : G | x ∈ K ⊓ normalizer (V₃ : Set G) ∧ orderOf x = 3} =
        sourceOne L T V₁ := by
  let N := K ⊓ normalizer (V₃ : Set G)
  let Y := closure {x : G | x ∈ N ∧ orderOf x = 3}
  have hY : Y ≤ sourceOne L T V₁ := seed_normalizer_theta_le d h hH hcentral hKH
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := by
    apply le_trans ?_ (normalizer_le_primeOrderClosure_normalizer 3 N)
    apply le_trans ?_ inf_normalizer_le_normalizer_inf
    exact le_inf ((le_sup_right.trans hH.1.2).trans hKn)
      (d.seed_stable.trans (normalizer (V₃ : Set G)).le_normalizer)
  have hYr : primeRank 3 Y = 2 := (primeRank_primeOrderClosure 3 N).trans hrank
  let C := Section08.Source.starImage (sourceOne L T V₁) Y
  have hCr : primeRank 3 C = 2 := by
    have he := ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3)
      (QuotientGroup.mk' (pCore 2 (sourceOne L T V₁)))
      (show IsPGroup 2 (QuotientGroup.mk' (pCore 2 (sourceOne L T V₁))).ker by
        rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
      (Y.subgroupOf (sourceOne L T V₁))
    change primeRank 3 C = _ at he
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hY)] at he
    exact he.trans hYr
  have hbig : ¬ Nat.card C ≤ 3 := by
    intro hc
    have hb := primeRank_le_of_card_le_prime_pow (p := 3) (n := 1) (G := C) hc
    omega
  rcases NaturalModels.quotient_alternatives d with ⟨e, he⟩ | ⟨e, he⟩
  · obtain ⟨a⟩ := NaturalModels.ordinary_natural d e he
    have hc := Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.source_residual_quotient_card
      a (sourceOne L T V₁) rfl
    exact (hbig (hc ▸ C.card_le_card_group)).elim
  · obtain ⟨a⟩ := NaturalModels.covered_natural d e he
    have hq := a.one_quotient_card (CoverFactorization.source_factorization a)
    have hcard : Nat.card C ∣ 3 ^ 2 := by
      have hh := C.card_subgroup_dvd_card
      rw [hq] at hh
      exact hh
    obtain ⟨k, hk, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hcard
    have hk2 : k = 2 := by
      interval_cases k <;> simp_all
    have hCt : C = ⊤ := eq_of_le_of_card_ge le_top (by
      rw [card_top, hq, hc, hk2]; decide)
    refine ⟨⟨e⟩, le_antisymm hY ?_⟩
    apply le_of_point_residual_image_le d le_rfl
      (residual_isPPerfect (parabolic L T V₁)) hTY
    change _ ≤ C
    rw [hCt]
    exact le_top

/-- Original13.7.5(4) for the L₁-contained case; normality is proved, not assumed. -/
theorem covered_and_theta_of_one_le_rank_two
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (hrank : primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 2) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      closure {x : G | x ∈ K ⊓ normalizer (V₃ : Set G) ∧ orderOf x = 3} =
        sourceOne L T V₁ :=
  covered_and_theta_of_normal_component_rank_two d h hH hcentral hKH
    (component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K).1 hrank

/-- Original13.7.5(4) for the covered choice X=L₁,+. -/
theorem theta_of_plus_le_rank_two
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hplusK : plus L T V₁ ≤ K)
    (hrank : primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 2) :
    closure {x : G | x ∈ K ⊓ normalizer (V₃ : Set G) ∧ orderOf x = 3} =
      sourceOne L T V₁ :=
  (covered_and_theta_of_normal_component_rank_two d h hH hcentral hKH
    (component_normal_and_span_of_plus_le d hH hF9 hcover hKH hK hplusK).1 hrank).2

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
