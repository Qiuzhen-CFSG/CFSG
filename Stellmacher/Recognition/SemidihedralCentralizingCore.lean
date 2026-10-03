module

public import Stellmacher.Recognition.SemidihedralCentralizerQuotient
public import Stellmacher.Recognition.SemidihedralFourCentralizer
public import Stellmacher.Recognition.SemidihedralCentralizerOvergroupFusion
public import BenderSuzuki.SE.SingleInvolutionClass
public import Theory.GroupTheory.PPrimeCoreHall

/-!
# The centralizing-core normalizer argument

Let `K` be the ambient odd core of an involution centralizer `C_G(x)`.
If `K` centralizes a four-group `T` containing `x`, and `C_G(T)` has order
`4 |K|`, then `K` is the intrinsic odd core of `C_G(T)`. Thus `N_G(T)`
normalizes `K`. If the involutions of `N_G(K)` are fused there, its containment
of `C_G(x)` makes it strongly embedded whenever it is proper. The odd-core
consequence of Bender--Suzuki rules this out, and simplicity gives `K = 1`.

For a finite simple N₂-group with semidihedral Sylow two-subgroups, the
local quotient `C_G(x)/O(C_G(x)) ≃ GL₂(3)` supplies this centralizer order,
and semidihedral fusion supplies the single involution class. The final
theorem therefore eliminates the odd core whenever it centralizes `T`.

Source: Alperin--Brauer--Gorenstein, III.7 Proposition 8 and Corollary 2,
article p.110, and III.8 Proposition 5, article p.117.
-/

namespace Stellmacher.Recognition

/-- The full involution centralizer normalizes its ambient odd core. -/
public theorem involutionCentralizer_le_normalizer_oddCore
    {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype : Set G) := by
  exact Subgroup.le_normalizer.trans
    (Subgroup.normalizer_le_normalizer_characteristic_image _ _)

/-- The local order formula identifies the centralizing core intrinsically,
so the entire four-group normalizer preserves it. -/
public theorem fourNormalizer_le_normalizer_oddCore_of_centralizer_card
    {G : Type*} [Group G] [Finite G]
    (x : G) (T : Subgroup G) (hxT : x ∈ T)
    (hcentral : (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
      (Subgroup.centralizer ({x} : Set G)).subtype ≤ Subgroup.centralizer (T : Set G))
    (hcard : Nat.card (Subgroup.centralizer (T : Set G)) =
      4 * Nat.card (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)))) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer
      ((pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype : Set G) := by
  let C := Subgroup.centralizer ({x} : Set G)
  let K := (pPrimeCore 2 C).map C.subtype
  have hKcard : Nat.card K = Nat.card (pPrimeCore 2 C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  refine Subgroup.normalizer_le_normalizer_of_centralizer_hall 2 T K hcentral
    ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxT)).trans
      (involutionCentralizer_le_normalizer_oddCore x)) ?_ 2 ?_
  · rw [hKcard]
    exact pPrimeCore_coprime_card
  · simpa [hKcard, C] using hcard

/-- Once its normalizer fuses all involutions to the chosen involution, the
centralizer odd core vanishes. -/
public theorem involutionCentralizer_oddCore_eq_bot_of_normalizer_fusion
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (x : G) (hx : orderOf x = 2)
    (hfusion :
      let K := (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype
      ∀ y ∈ Subgroup.normalizer (K : Set G), orderOf y = 2 →
        ∃ m ∈ Subgroup.normalizer (K : Set G), m * x * m⁻¹ = y) :
    pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ := by
  let C := Subgroup.centralizer ({x} : Set G)
  let K := (pPrimeCore 2 C).map C.subtype
  have hodd : Odd (Nat.card K) := by
    rw [show Nat.card K = Nat.card (pPrimeCore 2 C) from
      Subgroup.card_map_of_injective C.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hKbot := BenderSuzuki.odd_subgroup_eq_bot_of_normalizer_single_involution_class
    K hodd x hx (involutionCentralizer_le_normalizer_oddCore x) hfusion
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hKbot

/-- Assembly of the local order computation and the overgroup fusion step. -/
public theorem involutionCentralizer_oddCore_eq_bot_of_centralizer_card_and_fusion
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (x : G) (hx : orderOf x = 2) (T : Subgroup G) (hxT : x ∈ T)
    (hcentral : (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
      (Subgroup.centralizer ({x} : Set G)).subtype ≤ Subgroup.centralizer (T : Set G))
    (hcard : Nat.card (Subgroup.centralizer (T : Set G)) =
      4 * Nat.card (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))))
    (hfusion : ∀ M : Subgroup G, Subgroup.centralizer ({x} : Set G) ≤ M →
      Subgroup.normalizer (T : Set G) ≤ M →
      ∀ y ∈ M, orderOf y = 2 → ∃ m ∈ M, m * x * m⁻¹ = y) :
    pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ := by
  apply involutionCentralizer_oddCore_eq_bot_of_normalizer_fusion x hx
  exact hfusion _ (involutionCentralizer_le_normalizer_oddCore x)
    (fourNormalizer_le_normalizer_oddCore_of_centralizer_card x T hxT hcentral hcard)

/-- In the simple semidihedral N₂ branch, an involution-centralizer odd core
that centralizes a four-group containing the involution is trivial. This is
the centralizing-core step of ABG III.8 Proposition 5. -/
public theorem involutionCentralizer_oddCore_eq_bot_of_centralizing_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T)
    (hcentral : (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
      (Subgroup.centralizer ({x} : Set G)).subtype ≤ Subgroup.centralizer (T : Set G)) :
    pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ := by
  exact involutionCentralizer_oddCore_eq_bot_of_centralizer_card_and_fusion
    x hx T hxT hcentral
    (fourCentralizer_card_of_simple_nTwo S hS hN x hx T hT hxT hcentral)
    (involution_fusion_of_semidihedral_centralizer_and_four_normalizer
      S hS x hx T hT hxT)

end Stellmacher.Recognition
