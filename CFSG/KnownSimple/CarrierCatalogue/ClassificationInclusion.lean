module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ClassificationModels.ConstructedInclusion

/-!
# Inclusion of the quasithin outputs in the full known-simple catalogue

The existing Main Theorem, Theorems 2.1.1/D/E, and Even Type output lists
all use carriers present in the full catalogue. We retain each actual
isomorphism witness and check its field-size and rank restrictions. The
small derived groups, triality action and eleven sporadic outputs use the
same constructions on both sides, so no recognition theorem is needed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Main
Theorem (pp. 4 and 482), Even Type Theorem (p. 483), Remark A.2.4, and GLS3,
Theorem 2.2.7 and Definition 2.2.8 for the full simple parameter ranges.
These are inclusions of independently specified catalogues, not proofs of
the classification or of the proper-K condition for a model.
-/

public section

namespace CFSG.Quasithin.ClassificationModels

open CFSG.KnownSimple

variable {G : Type*} [Group G]

private theorem primePow_two {f : ℕ} (hf : 1 ≤ f) : IsPrimePow (2 ^ f) :=
  Nat.prime_two.isPrimePow.pow (by omega)

private theorem four_le_two_pow {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  pow_le_pow_right' (show 1 ≤ (2 : ℕ) by decide) hf

theorem IsG2At.isKnownSimpleCarrier {q : ℕ} (h : IsG2At G q) (hq : 2 < q) :
    IsKnownSimpleCarrier G := by
  obtain ⟨F, hF, hfin, hcard, iso⟩ := h
  exact .g2 ⟨F, hF, hfin, by omega, iso⟩

theorem IsBenderModel.isKnownSimpleCarrier (h : IsBenderModel G) :
    IsKnownSimpleCarrier G := by
  cases h with
  | linear f hf iso =>
      exact .classical (.linear 2 (2 ^ f)
        ⟨primePow_two (by omega), by decide, fun _ => four_le_two_pow hf⟩ iso)
  | unitary f hf iso =>
      have hq := four_le_two_pow hf
      exact .classical (.unitary 3 (2 ^ f)
        ⟨primePow_two (by omega), by decide, by omega, by omega⟩ iso)
  | suzuki m hm iso => exact .suzuki m hm iso

theorem IsRankTwoModel.isKnownSimpleCarrier {f : ℕ} (h : IsRankTwoModel G f) :
    IsKnownSimpleCarrier G := by
  cases h with
  | linear hf iso =>
      exact .classical (.linear 3 (2 ^ f) ⟨primePow_two hf, by decide, by omega⟩ iso)
  | unitary_four hf iso =>
      exact .classical (.unitary 4 (2 ^ f)
        ⟨primePow_two hf, by decide, by omega, by omega⟩ iso)
  | unitary_five hf iso =>
      exact .classical (.unitary 5 (2 ^ f)
        ⟨primePow_two (by omega), by decide, by omega, by omega⟩ iso)
  | symplectic hf iso =>
      have hq := four_le_two_pow hf
      exact .classical (.symplectic 2 (2 ^ f)
        ⟨primePow_two (by omega), by decide, by omega, by omega⟩ iso)
  | g2 hf iso =>
      exact iso.isKnownSimpleCarrier (lt_of_lt_of_le (by decide) (four_le_two_pow hf))
  | triality _ iso =>
      obtain ⟨P, _, iso⟩ := iso
      exact .triality ⟨P, iso⟩
  | ree_f4 m hm _ iso => exact .reeF4 ⟨m, hm, iso⟩
  | symplectic_derived _ iso => exact .smallDerived (.symplectic iso)
  | g2_derived _ iso => exact .smallDerived (.g2 iso)
  | tits _ iso => exact .smallDerived (.tits iso)

theorem IsSporadicModel.isKnownSimpleCarrier (h : IsSporadicModel G) :
    IsKnownSimpleCarrier G := by
  obtain ⟨name, iso⟩ := h
  apply IsKnownSimpleCarrier.sporadic
  cases name with
  | m11 => exact ⟨.m11, iso⟩
  | m12 => exact ⟨.m12, iso⟩
  | m22 => exact ⟨.m22, iso⟩
  | m23 => exact ⟨.m23, iso⟩
  | m24 => exact ⟨.m24, iso⟩
  | j2 => exact ⟨.j2, iso⟩
  | j3 => exact ⟨.j3, iso⟩
  | j4 => exact ⟨.j4, iso⟩
  | hs => exact ⟨.hs, iso⟩
  | he => exact ⟨.he, iso⟩
  | ru => exact ⟨.ru, iso⟩

/-- Every complete Main Theorem output belongs to the full carrier catalogue. -/
theorem IsQTKEModel.isKnownSimpleCarrier (h : IsQTKEModel G) :
    IsKnownSimpleCarrier G := by
  cases h with
  | bender h => exact h.isKnownSimpleCarrier
  | rank_two _ h => exact h.isKnownSimpleCarrier
  | linear_binary n hn iso =>
      exact .classical (.linear n 2 ⟨Nat.prime_two.isPrimePow, by omega, by omega⟩ iso)
  | symplectic_binary iso =>
      exact .classical (.symplectic 3 2
        ⟨Nat.prime_two.isPrimePow, by decide, by omega, by omega⟩ iso)
  | alternating n hn iso => exact .alternating n (by omega) iso
  | linear_prime p hp hlarge iso =>
      exact .classical (.linear 2 p ⟨hp.1.isPrimePow, by decide, by omega⟩ iso)
  | linear_three n hn iso =>
      exact .classical (.linear n 3 ⟨Nat.prime_three.isPrimePow, by omega, by omega⟩ iso)
  | unitary_three n hn iso =>
      exact .classical (.unitary n 3
        ⟨Nat.prime_three.isPrimePow, by omega, by omega, by omega⟩ iso)
  | g2_three iso => exact iso.isKnownSimpleCarrier (by decide)
  | sporadic h => exact h.isKnownSimpleCarrier

theorem IsQTKEModel.isKnownSimple [Finite G] [IsSimpleGroup G] (h : IsQTKEModel G) :
    IsKnownSimple G := isKnownSimple_iff_carrier.mpr h.isKnownSimpleCarrier

theorem IsTheorem211Model.isKnownSimpleCarrier (h : IsTheorem211Model G) :
    IsKnownSimpleCarrier G := h.toQTKEModel.isKnownSimpleCarrier

theorem IsTheoremDModel.isKnownSimpleCarrier (h : IsTheoremDModel G) :
    IsKnownSimpleCarrier G := h.toQTKEModel.isKnownSimpleCarrier

theorem IsTheoremEModel.isKnownSimpleCarrier (h : IsTheoremEModel G) :
    IsKnownSimpleCarrier G := h.toQTKEModel.isKnownSimpleCarrier

theorem IsEvenTypeModel.isKnownSimpleCarrier (h : IsEvenTypeModel G) :
    IsKnownSimpleCarrier G := by
  rcases h with h | h
  · exact h.isKnownSimpleCarrier
  · exact .sporadic ⟨.j1, h⟩

end CFSG.Quasithin.ClassificationModels

namespace CFSG.Quasithin

/-- Compatibility with the earlier partial output interface. -/
theorem IsConstructedQTKEModel.isKnownSimpleCarrier {G : Type*} [Group G]
    (h : IsConstructedQTKEModel G) : KnownSimple.IsKnownSimpleCarrier G :=
  h.toQTKEModel.isKnownSimpleCarrier

end CFSG.Quasithin
