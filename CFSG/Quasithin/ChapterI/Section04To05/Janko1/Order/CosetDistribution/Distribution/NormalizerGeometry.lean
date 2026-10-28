module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.NormalizerGeometry.InvertedOrders
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.NormalizerGeometry.LocalStructure
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.NormalizerGeometry.InversionClosure
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.NormalizerGeometry.Census

/-!
# Constructing Bender's normalizer geometry

Pairwise commutation of the elements inverted by an outside involution gives
closure of the literal inversion set. The four-group overlap argument and
assertion (4.3) then restrict its order to one, two, three, six or seven.
The imported fiber theorem applies this to the literal right-coset convention.

The overlap analysis proves pairwise commutation, including the nonabelian
order-21 case. Sylow theory and the free action of the Sylow eight-group on
seven-subgroups give the census and its fixed-point count. Together with
cyclicity of every six-subgroup and the order-six centralizer of every
three-subgroup, these construct `bender_normalizerGeometry` from the supplied
local and normalizer data. Its `fiber_sizes_with_two` theorem supplies the
geometry premise used by `bender_distributionData_of_incidence_counts`.

Source: Bender, *Finite groups with large subgroups* (1974), §4, printed
pp.226–227, the subgroup geometry following (4.3).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (h : Janko1CentralizerData G)

public theorem bender_normalizerGeometry_of_pairwise_commute_and_census
    {d : ℕ} (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h)
    (hcomm : ∀ u : G, orderOf u = 2 → u ∉ normalizer (h.sylow : Set G) →
      ∀ a b : G, a ∈ normalizer (h.sylow : Set G) →
        b ∈ normalizer (h.sylow : Set G) → u * a * u⁻¹ = a⁻¹ →
        u * b * u⁻¹ = b⁻¹ → Commute a b)
    (hthree : Nat.card (BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3) = 28)
    (hsix : Nat.card (BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 6) = 28)
    (hseven : Nat.card (BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7) = 8)
    (hnorm : ∀ X : Subgroup G, X ≤ normalizer (h.sylow : Set G) → Nat.card X = 3 →
      Nat.card {S : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 7 //
        X ≤ normalizer (S.1 : Set G)} = 2) : BenderNormalizerGeometry h where
  inverted_subgroup u hu huH := h.bender_inverted_subgroup_of_pairwise_commute
    normalizerData u hu huH (hcomm u hu huH)
  three_subgroups := hthree
  six_subgroups := hsix
  seven_subgroups := hseven
  six_cyclic := h.bender_six_cyclic
  three_centralizer := h.bender_three_centralizer localData normalizerData
  three_normalizes_seven := hnorm

/-- Bender's subgroup geometry for the actual Sylow normalizer, from the
supplied local prime data and normalizer conclusions. This discharges the
geometry premise of the inversion-incidence distribution assembly. -/
public theorem bender_normalizerGeometry
    {d : ℕ} (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h) :
    BenderNormalizerGeometry h :=
  h.bender_normalizerGeometry_of_pairwise_commute_and_census localData normalizerData
    (h.bender_inverted_elements_commute localData normalizerData)
    (h.bender_three_subgroups localData normalizerData)
    (h.bender_six_subgroups localData normalizerData)
    (h.bender_seven_subgroups normalizerData)
    (h.bender_three_normalizes_seven localData normalizerData)

end CFSG.Quasithin.Janko1CentralizerData
