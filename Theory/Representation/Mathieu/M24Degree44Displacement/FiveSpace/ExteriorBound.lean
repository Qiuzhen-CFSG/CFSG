module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.ExteriorBound.Permutation
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.ExteriorBound.CyclicBasis

/-!
# The native Golay exterior calculation from cyclic basis classification

An order-five operator in dimension eleven with fixed dimension three has
cyclic module type `1³ ⊕ Φ₅²`, hence a permutation basis of type `5 + 5 + 1`.
The separate permutation calculation bounds the literal exterior-square fixed
space by eleven. Here we apply it to the original code and cocode actions,
using their already proved fixed dimensions, and feed the result to the
actual degree-44 section consumer.

The proved cyclic basis classification discharges the last premise of
`golayExteriorFiveBound`. The degree-44 application retains only universal
section placement, whose proof belongs to the separate placement development.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17.
-/

public section
universe v
namespace Representation.MathieuM24Degree44.FiveSpace
open Sporadic.Mathieu BinaryOffender
open ExteriorBound

/-- An actual cyclic permutation basis controls the functorial exterior action. -/
theorem exterior_fixed_finrank_le_of_permutationBasis
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (x : G)
    (hb : HasPermutationBasis (ρ x)) :
    Module.finrank (ZMod 2) (fixedSpace (exteriorSquare ρ) (Subgroup.zpowers x)) ≤ 11 := by
  obtain ⟨b, hb⟩ := hb
  have hk : LinearMap.ker (exteriorPower.map 2 (ρ x) - 1) =
      fixedSpace (exteriorSquare ρ) (Subgroup.zpowers x) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero
  rw [← hk]
  exact exterior_fixed_finrank_le (ρ x) b hb

/-- The remaining classification premise concerns only the original
11-dimensional binary operator, and contains no exterior-square bound. -/
theorem golayExteriorFiveBound_of_cyclicBasis (hbasis : CyclicBasisClassification.{0}) :
    GolayExteriorFiveBound := by
  intro x hx
  have hp (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) M24 V) : (ρ x) ^ 5 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hfix (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) M24 V) :
      LinearMap.ker (ρ x - 1) = fixedSpace ρ (Subgroup.zpowers x) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero
  constructor
  · apply exterior_fixed_finrank_le_of_permutationBasis
    apply hbasis (MathieuCode.codeRepresentation x) (hp _ _) MathieuCode.finrank_code
    rw [hfix]
    exact code_five_fixed_finrank x hx
  · apply exterior_fixed_finrank_le_of_permutationBasis
    apply hbasis (MathieuCode.cocodeRepresentation x) (hp _ _) MathieuCode.finrank_cocode
    rw [hfix]
    exact cocode_five_fixed_finrank x hx

/-- Every order-five element fixes at most eleven dimensions on each literal
exterior square of the native binary Golay code and cocode. -/
theorem golayExteriorFiveBound : GolayExteriorFiveBound :=
  golayExteriorFiveBound_of_cyclicBasis cyclicBasisClassification

/-- Consumer application: once cyclic basis classification and section
placement are supplied, the native degree-44 five-space contract follows. -/
theorem fiveFixedSpaceBound_of_cyclicBasis
    (hplacement : GolayExteriorPlacement.{v}) (hbasis : CyclicBasisClassification.{0}) :
    FiveFixedSpaceBound.{v} :=
  fiveFixedSpaceBound_of_golay_exterior hplacement
    (golayExteriorFiveBound_of_cyclicBasis hbasis)

/-- The native exterior calculation discharges the order-five premise of the
degree-44 section argument; only universal section placement remains. -/
theorem fiveFixedSpaceBound_of_placement (hplacement : GolayExteriorPlacement.{v}) :
    FiveFixedSpaceBound.{v} :=
  fiveFixedSpaceBound_of_golay_exterior hplacement golayExteriorFiveBound

end Representation.MathieuM24Degree44.FiveSpace
