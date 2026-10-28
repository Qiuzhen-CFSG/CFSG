module

public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.InvariantEight
public import Theory.GroupTheory.ElementaryEightFixedPointOrder24

/-!
# The action on the source eight and its centralizer bound

The conjugation action is that of the actual involution centralizer on
`U = ⟨Z_S^H⟩`. Its kernel is the actual `C_H(U)`. The action fixes the
involution in `Z(P)`, so its image order divides 24; since `|H| = 384`,
`|C_H(U)|` is a multiple of 16. This supplies the lower divisibility bound
for the geometric extension of the p.688 M₂₂ branch. The exact order still
requires the extraspecial pairing and the quotient `H/P ≃ S₃ × C₂`.
-/

namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension

open Subgroup

variable {H : Type*} [Group H]

/-- Actual conjugation on the normal closure inside `H`. -/
@[expose] public def sourceEightAction (S : Subgroup H) : H →* MulAut (sourceEight S) :=
  (sourceEight S).normalizerMonoidHom.comp {
    toFun := fun h => ⟨h, (sourceEight S).normalizer_eq_top ▸ mem_top h⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

public theorem sourceEightAction_ker (S : Subgroup H) :
    (sourceEightAction S).ker = centralizer (sourceEight S : Set H) := by
  ext h
  change (⟨h, _⟩ : normalizer (sourceEight S : Set H)) ∈
    (sourceEight S).normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

variable [Finite H] {P S : Subgroup H} [P.Normal]

/-- Fixing the central involution bounds the actual action image. -/
public theorem sourceEightAction_card_dvd_twentyfour
    (h : CoreData P) (ha : NaturalFourOrbit P S)
    [IsElementaryAbelian 2 S] (hS : Nat.card S = 4) (hZS : coreCenter P ≤ S) :
    Nat.card (sourceEightAction S).range ∣ 24 := by
  let := sourceEight_elementary h ha hS
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : coreCenter P)).mp (coreCenter_card h)
  let zU : sourceEight S := ⟨z, sourceEight_contains S (hZS z.property)⟩
  have hzU : zU ≠ 1 := by
    intro he
    exact hz (Subtype.ext (show (z : H) = 1 from congrArg Subtype.val he))
  apply elementaryEight_fixed_point_image_card_dvd_twentyfour
    (sourceEight_card h ha hZS) zU hzU
  rintro ⟨a, g, rfl⟩
  apply Subtype.ext
  change g * (z : H) * g⁻¹ = z
  rw [mem_center_iff.mp (h.center_le z.property), mul_inv_cancel_right]

/-- The source centralizer order is a multiple of sixteen, without any
assumed centralizer size or elementary-sixteen subgroup. -/
public theorem sourceEight_centralizer_card_multiple_sixteen
    (h : CoreData P) (ha : NaturalFourOrbit P S)
    [IsElementaryAbelian 2 S] (hS : Nat.card S = 4) (hZS : coreCenter P ≤ S) :
    16 ∣ Nat.card (centralizer (sourceEight S : Set H)) := by
  let f := sourceEightAction S
  have hc : Nat.card (centralizer (sourceEight S : Set H)) * Nat.card f.range = 384 := by
    have he := f.ker.card_mul_index
    rw [index_ker, sourceEightAction_ker, h.card] at he
    exact he
  obtain ⟨n, hn⟩ := sourceEightAction_card_dvd_twentyfour h ha hS hZS
  refine ⟨n, Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.range)) ?_⟩
  calc
    Nat.card (centralizer (sourceEight S : Set H)) * Nat.card f.range = 384 := hc
    _ = 16 * 24 := rfl
    _ = 16 * (Nat.card f.range * n) := congrArg (16 * ·) hn
    _ = (16 * n) * Nat.card f.range := by ac_rfl

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
