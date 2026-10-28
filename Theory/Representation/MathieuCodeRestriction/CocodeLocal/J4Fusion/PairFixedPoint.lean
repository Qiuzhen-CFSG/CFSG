module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.PairNormalizer
/-!
# A pair stabilizer with trivial point stabilizer

Evaluation at a coordinate embeds a group preserving a pair in that pair
when no nonidentity element fixes the coordinate. This gives the order-two
bound used by the second J4 fixed-coset argument on the actual Todd image.
Source: Aschbacher–Segev (1991), proof of (6.3), p.602.
-/

public section
open Subgroup Sporadic.Mathieu
open scoped Pointwise
namespace MathieuCode.J4Fusion

/-- A subgroup preserving a pair and having trivial point stabilizer acts
faithfully on that pair, so has order at most two. -/
theorem pair_stabilizer_card_le_two (A : PointPair) (i : Fin 24) (hi : i ∈ A.val)
    (S : Subgroup M24)
    (hSA : S ≤ cocodeVectorStabilizer cocodeRepresentation (pairVector A))
    (hfix : ∀ s ∈ S, s • i = i → s = 1) : Nat.card S ≤ 2 := by
  classical
  let f : S → ↥A.val := fun s => ⟨s.val • i,by
    have hg : mapPair s.val A = A := pairVector_injective
      ((pairVector_equivariant s.val A).symm.trans (hSA s.property))
    have hs : s.val • A.val = A.val := congrArg Subtype.val hg
    rw [←hs]
    exact Finset.smul_mem_smul_finset hi⟩
  have hf : Function.Injective f := by
    intro s t he
    have hei : s.val • i = t.val • i := congrArg Subtype.val he
    have hc : t.val⁻¹ * s.val = 1 := hfix _ (S.mul_mem (S.inv_mem t.property) s.property)
      (by rw [mul_smul,hei,inv_smul_smul])
    exact Subtype.ext (inv_mul_eq_one.mp hc).symm
  have hh := Nat.card_le_card_of_injective f hf
  have hcard : Nat.card ↥A.val = 2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,A.property]
  rwa [hcard] at hh

end MathieuCode.J4Fusion
