module

public import Theory.GroupAction.FourthPowerFixedCard
public import Theory.GroupAction.SubgroupConjugation

/-!
# Centralizers of elements with fourth power centralizing an elementary group

If y normalizes an elementary binary subgroup E and y⁴ centralizes E,
conjugation by y has fourth power one on E. The fourth-root fixed-point
bound therefore bounds the actual ambient centralizer. For |E|=32 this
centralizer has more than two elements.

Source: the fixed-point calculation in Parrott (1972), pp.674–676.
No assertion about the order of y itself is needed.
-/

namespace Subgroup

/-- The ambient fixed-point count only needs the fourth power to
centralize E, not to be the identity in the ambient group. -/
public theorem two_lt_centralizer_card_of_card_thirty_two_of_fourth_power
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 32)
    (y : G) (hy : y ∈ normalizer (E : Set G))
    (hy4 : y ^ 4 ∈ centralizer (E : Set G)) :
    2 < Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) := by
  let Y := zpowers y
  let : MulDistribMulAction Y E := conjMulDistribMulActionOfLeNormalizer Y E
    (zpowers_le.mpr hy)
  let yY : Y := ⟨y, mem_zpowers y⟩
  let f := MulDistribMulAction.toMulAut Y E
  have hf : (f yY) ^ 4 = 1 := by
    rw [← map_pow]
    ext e
    change y ^ 4 * (e : G) * (y ^ 4)⁻¹ = (e : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hy4 e e.property).symm
  let F := FixedPoints.subgroup (zpowers (f yY)) E
  have hF : 2 < Nat.card F :=
    MulAut.two_lt_fixed_card_of_card_thirty_two_of_fourth_power_eq_one hE (f yY) hf
  let i : F → (E ⊓ centralizer ({y} : Set G) : Subgroup G) := fun e =>
    ⟨((e : E) : G), (e : E).property, mem_centralizer_singleton_iff.mpr (by
      have hh := congrArg E.subtype
        ((MulAut.mem_fixed_zpowers_iff (f yY) (e : E)).mp e.property)
      change y * ((e : E) : G) * y⁻¹ = ((e : E) : G) at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm)⟩
  have hi : Function.Injective i := by
    intro e e' he
    exact Subtype.ext (Subtype.ext (congrArg
      (fun x : (E ⊓ centralizer ({y} : Set G) : Subgroup G) => (x : G)) he))
  exact hF.trans_le (Nat.card_le_card_of_injective i hi)

end Subgroup
