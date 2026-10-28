module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Commuting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences.Counting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences.LocalInverters
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences.CentralizedSingletons

/-!
# Bender inversion-incidence assembly

The actual element-inverter counts for orders six and seven determine the
sextuple and septuple counts through the subgroup census. The supplied
prime data and commuting theorem independently determine the three/six and
two/six incidences. All four conclusions count literal ambient involutions
in the quotient fibers.

The final theorem constructs the uniform local inverter counts and combines
these four incidences with the commuting-three singleton count. Its five
equations are exactly the inputs of `bender_distributionData_of_incidence_counts`.
Only the supplied prime data, normalizer data and subgroup geometry remain
as source inputs; no incidence or distribution premise is assumed.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed pp.226–227, following (4.3).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- The ambient six- and seven-inverter counts imply all four inversion
incidences. The centralization count is a separate source argument. -/
public theorem bender_inversion_counts_of_uniform_inverters
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (d e : ℕ)
    (localData : BenderPrimeData G d) (geometry : BenderNormalizerGeometry h)
    (hseven : ∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = 7 →
      Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} = 7 * e)
    (hsix : ∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = 6 →
      Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} = 6) :
    Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 7) = 56 * e ∧
    Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168 ∧
    Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 3) +
      Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168 * d ∧
    Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 2) +
      Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168 := by
  have h7 := bender_inversion_incidence_identity h geometry 7 (7 * e) (by
    intro x hx
    rw [bender_outside_inverting_card h x (by rw [hx]; decide)]
    exact hseven x hx)
  have hc7 := bender_order_elements_card (normalizer (h.sylow : Set G)) 7 (by
    intro S _ hS
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact isCyclic_of_prime_card (p := 7) hS)
  rw [geometry.seven_subgroups] at hc7
  norm_num [show Nat.totient 7 = 6 by decide] at h7 hc7
  rw [hc7] at h7
  have h6 := bender_inversion_incidence_identity h geometry 6 6 (by
    intro x hx
    rw [bender_outside_inverting_card h x (by rw [hx]; decide)]
    exact hsix x hx)
  have hc6 := bender_order_elements_card (normalizer (h.sylow : Set G)) 6
    geometry.six_cyclic
  rw [geometry.six_subgroups] at hc6
  norm_num [show Nat.totient 6 = 2 by decide] at h6 hc6
  rw [hc6] at h6
  exact ⟨by omega, by omega, bender_three_inversion_incidence h d localData geometry,
    bender_two_inversion_incidence h geometry⟩

/-- Bender's five ambient inversion and centralization incidences following (4.3).
The uniform local inverter counts and the singleton incidence are proved inputs;
the three supplied records retain the earlier source and normalizer geometry. -/
public theorem bender_inversion_incidence_counts
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (d : ℕ)
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h)
    (geometry : BenderNormalizerGeometry h) :
    ∃ e : ℕ, e ≤ 1 ∧
      Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 7) = 56 * e ∧
      Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168 ∧
      Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 3) +
        Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168 * d ∧
      Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 2) +
        Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168 ∧
      Nat.card (BenderCentralizedSingletons (normalizer (h.sylow : Set G))) +
        56 * (1 + e) = 56 * d := by
  obtain ⟨e, he, hseven, hsix⟩ :=
    bender_uniform_local_inverter_counts h normalizerData geometry
  obtain ⟨h7, h6, h3, h2⟩ :=
    bender_inversion_counts_of_uniform_inverters h d e localData geometry hseven hsix
  exact ⟨e, he, h7, h6, h3, h2,
    bender_centralized_singleton_incidence h d e localData normalizerData geometry he hseven⟩

end CFSG.Quasithin.Janko1CentralizerData
