module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.OddCore
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.NormalizerCubicCentralizer

/-!
# The original cubic quotient has a nontrivial three-part

The full normalizer of the specified original sixteen has cubic centralizer
of order eighteen. Its inclusion in the ambient cubic centralizer, whose
odd core is exactly the original cubic subgroup, forces three to divide the
order of the actual odd-core quotient. This excludes the two-group branch
without an ambient centralizer model.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V A : Subgroup G}

/-- The actual quotient of the original cubic centralizer by its whole odd
core has order divisible by three. -/
theorem TypeAt.cubic_centralizer_quotient_three_dvd (h : TypeAt z V)
    [IsElementaryAbelian 2 A] (d : NaturalEndpointData A) (t : G)
    (htz : t ∈ involutionCentralizer z) (ht : t ∈ d.carrier) (ht3 : orderOf t = 3) :
    3 ∣ Nat.card ((centralizer ({t} : Set G)) ⧸
      pPrimeCore 2 (centralizer ({t} : Set G))) := by
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  have hO : Nat.card O = 3 := by
    calc
      Nat.card O = Nat.card (O.map C.subtype) := (card_map_of_injective C.subtype_injective).symm
      _ = Nat.card (zpowers t) := by rw [h.cubic_centralizer_oddCore t htz ht3]
      _ = 3 := (Nat.card_zpowers t).trans ht3
  have h18 : 18 ∣ Nat.card C := by
    rw [← (d.cubic_full_normalizer_centralizer t ht ht3).1]
    exact card_dvd_of_le (show normalizer (A : Set G) ⊓ C ≤ C from inf_le_right)
  have hcard := O.card_eq_card_quotient_mul_card_subgroup
  rw [hO] at hcard
  rw [hcard] at h18
  obtain ⟨n, hn⟩ := h18
  change 3 ∣ Nat.card (C ⧸ O)
  exact ⟨2*n, by omega⟩

end CFSG.Quasithin.HigmanSims
