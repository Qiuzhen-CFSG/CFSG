module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split.Actions
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Normalizer
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Order
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Actual Weyl elements for the split three-primary torus

Choose a Sylow three inside the existing split torus and use its literal
subtype image in BinaryCarrier. The Weyl rotation r² has order three and
lies outside the torus, by Bruhat-cell separation. It normalizes the primary
torus because a Sylow subgroup of an abelian group is characteristic.
The central Weyl involution r³ inverts that torus and commutes with r².

The primary generator pair remains a separate construction; no ambient
Sylow assertion or conclusion about central covers is an input here.

Source: GLS3 §§2.3–2.4 and the nondefining-characteristic calculation
underlying §6.1, Theorem 6.1.4 and Tables 6.1.2–3.
-/

@[expose] public section
noncomputable section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split
open Standard Standard.Parabolics Standard.ConcreteBruhat
open Standard.ConcreteBruhat.TorusCoordinates

/-- A Sylow three of the existing split torus, before its ambient image. -/
def primary (n : ℕ) (hn : 0 < n) : Sylow 3 (torus (binaryParameters n hn)) :=
  Classical.choice inferInstance

/-- The literal subtype image of the chosen primary torus. -/
def primaryImage (n : ℕ) (hn : 0 < n) : Subgroup (BinaryCarrier n hn) :=
  ((primary n hn : Subgroup (torus (binaryParameters n hn)))).map
    (torus (binaryParameters n hn)).subtype

/-- The order-three rotation in the faithful relative Weyl subgroup. -/
def cycle (n : ℕ) (hn : 0 < n) : BinaryCarrier n hn :=
  weylRepresentative (binaryParameters n hn) rfl (.r 2)

/-- The central involution of the relative Weyl subgroup. -/
def inverter (n : ℕ) (hn : 0 < n) : BinaryCarrier n hn :=
  weylRepresentative (binaryParameters n hn) rfl (.r 3)

theorem primaryImage_le_torus (n : ℕ) (hn : 0 < n) :
    primaryImage n hn ≤ torus (binaryParameters n hn) := by
  rintro _ ⟨t, _, rfl⟩
  exact t.property

theorem cycle_order (n : ℕ) (hn : 0 < n) : orderOf (cycle n hn) = 3 := by
  exact (orderOf_weylRepresentative (binaryParameters n hn) rfl (.r 2)).trans
    (by norm_num [DihedralGroup.orderOf_r, show (2 : ZMod 6).val = 2 from rfl])

theorem cycle_outside (n : ℕ) (hn : 0 < n) : cycle n hn ∉ primaryImage n hn := by
  intro h
  have hB := torus_le_borel (binaryParameters n hn) (primaryImage_le_torus n hn h)
  have he := (RelativeNormalizer.representative_mem_borel_iff n hn (.r 2)).mp hB
  exact (by decide : (DihedralGroup.r (2 : ZMod 6)) ≠ 1) he

theorem cycle_normalizes (n : ℕ) (hn : 0 < n) :
    cycle n hn ∈ Subgroup.normalizer (primaryImage n hn : Set (BinaryCarrier n hn)) := by
  let P := binaryParameters n hn
  let : IsMulCommutative (torus P) := by
    apply IsMulCommutative.of_comm
    intro a b
    apply (torusMulEquiv P rfl).symm.injective
    simp only [map_mul, mul_comm]
  let : (primary n hn : Subgroup (torus P)).Characteristic :=
    Sylow.characteristic_of_normal (primary n hn) inferInstance
  exact Subgroup.normalizer_le_normalizer_characteristic_image (torus P)
    (primary n hn : Subgroup (torus P))
    (RelativeNormalizer.weylRepresentative_normalizes_torus P rfl (.r 2))

theorem inverter_inverts (n : ℕ) (hn : 0 < n) (t : BinaryCarrier n hn)
    (ht : t ∈ primaryImage n hn) : inverter n hn * t * (inverter n hn)⁻¹ = t⁻¹ := by
  let P := binaryParameters n hn
  obtain ⟨⟨x,y⟩, hxy⟩ := (torusMulEquiv P rfl).surjective
    ⟨t, primaryImage_le_torus n hn ht⟩
  have he : torusElement P rfl x y = t := congrArg Subtype.val hxy
  rw [← he]
  exact inverter_torusElement_conjugation P rfl x y

theorem inverter_commutes_cycle (n : ℕ) (hn : 0 < n) :
    Commute (inverter n hn) (cycle n hn) := by
  exact (show Commute (DihedralGroup.r (3 : ZMod 6)) (.r 2) by
      change DihedralGroup.r (3 : ZMod 6) * .r 2 = .r 2 * .r 3
      decide).map
    (weylRepresentativeHom (binaryParameters n hn) rfl)

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split
