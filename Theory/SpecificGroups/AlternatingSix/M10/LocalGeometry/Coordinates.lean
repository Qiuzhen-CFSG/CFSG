module
public import Theory.SpecificGroups.AlternatingSix.M10.Contracts
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry.Coordinates
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Coordinates for the marked M₁₀ local calculation

The subgroup of the cyclic-eight holomorph with multipliers 1 and 3 is
semidihedral of order sixteen. Its two marked generators map to the
exceptional rotation and the transposition (02) in Aut(A₆). The two disjoint
three-cycles below specify the nine-group used for the local calculation.

Source: Aschbacher, A 2-local characterization of M12 (2003), 4.9–4.10,
pp.41–42. All finite identities are checked by the Lean kernel.
-/

@[expose] public section
namespace AlternatingSix.M10.LocalGeometry
open Subgroup ShadowLocal

namespace Coordinates
open Holomorph

/-- The multiplier-three involution in the cyclic-eight holomorph. -/
def flip : Model := transposition * reflection

/-- The semidihedral subgroup, specified by its actual multipliers. -/
def complement : Subgroup Model where
  carrier := {x | (x.right : ZMod 8) = 1 ∨ (x.right : ZMod 8) = 3}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

instance : DecidablePred (· ∈ complement) := fun x =>
  inferInstanceAs (Decidable ((x.right : ZMod 8) = 1 ∨ (x.right : ZMod 8) = 3))

instance : Fintype complement := Subtype.fintype _

theorem card_complement : Nat.card complement = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem rotation_mem : rotation ∈ complement := by decide +kernel
theorem flip_mem : flip ∈ complement := by decide +kernel

def rotationIn : complement := ⟨rotation, rotation_mem⟩
def flipIn : complement := ⟨flip, flip_mem⟩

theorem rotationIn_order : orderOf rotationIn = 8 := by
  rw [← Subgroup.orderOf_coe]
  exact Holomorph.rotation_order

theorem flipIn_order : orderOf flipIn = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

theorem flipIn_rotationIn : flipIn * rotationIn * flipIn⁻¹ = rotationIn ^ 3 := by
  decide +kernel

theorem complement_normal_form (x : Model) (hx : x ∈ complement) :
    ∃ (i : Fin 8) (j : Fin 2), x = rotation ^ i.val * flip ^ j.val := by
  revert x
  decide +kernel

theorem complement_generated : zpowers rotationIn ⊔ zpowers flipIn = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, j, h⟩ := complement_normal_form x x.property
  have he : x = rotationIn ^ i.val * flipIn ^ j.val := Subtype.ext h
  rw [he]
  exact mul_mem_sup (Subgroup.pow_mem _ (mem_zpowers _) _)
    (Subgroup.pow_mem _ (mem_zpowers _) _)

theorem center_complement : (center complement).map complement.subtype = centralTwo := by
  ext x
  rw [centralTwo_eq_pair]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hc := mem_center_iff.mp ha
    have h : ∀ a : complement, (∀ b : complement, b * a = a * b) →
        (a : Model) = 1 ∨ (a : Model) = rotation ^ 4 := by decide +kernel
    exact h a hc
  · intro hx
    have hc : ∀ a : Model, a = 1 ∨ a = rotation ^ 4 →
        ∃ ha : a ∈ complement, (⟨a, ha⟩ : complement) ∈ center complement := by
      decide +kernel
    obtain ⟨ha, hc⟩ := hc x hx
    exact ⟨⟨x, ha⟩, hc, rfl⟩

theorem reflection_not_mem : reflection ∉ complement := by decide +kernel

theorem reflection_normalizes : reflection ∈ normalizer (complement : Set Model) := by
  rw [mem_normalizer_iff]
  decide +kernel

/-- The quaternion subgroup has even rotations over multiplier 1 and odd
rotations over multiplier 3. -/
def quaternionEmbedding : QuaternionGroup 2 →* Model where
  toFun
    | .a i => (rotation ^ 2) ^ i.val
    | .xa i => (rotation * flip) * (rotation ^ 2) ^ i.val
  map_one' := rfl
  map_mul' := by decide +kernel

theorem quaternionEmbedding_injective : Function.Injective quaternionEmbedding := by
  decide +kernel

end Coordinates

/-- The first three-cycle, on the even-numbered letters. -/
def cycle₀ : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 2 4
/-- The second three-cycle, on the odd-numbered letters. -/
def cycle₁ : Equiv.Perm (Fin 6) := Equiv.swap 1 3 * Equiv.swap 3 5

abbrev NineCoordinates := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

/-- A genuine embedding of C₃ × C₃ into the six-letter permutation group. -/
def nineEmbedding : NineCoordinates →* Equiv.Perm (Fin 6) where
  toFun x := cycle₀ ^ x.1.toAdd.val * cycle₁ ^ x.2.toAdd.val
  map_one' := rfl
  map_mul' := by decide +kernel

theorem nineEmbedding_injective : Function.Injective nineEmbedding := by decide +kernel

def standardNine : Subgroup (Equiv.Perm (Fin 6)) := nineEmbedding.range

theorem card_standardNine : Nat.card standardNine = 9 := by
  rw [standardNine, ← Nat.card_congr (MonoidHom.ofInjective nineEmbedding_injective).toEquiv]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def standardZ : Equiv.Perm (Fin 6) := Equiv.swap 0 2
def standardU : Equiv.Perm (Fin 6) := Equiv.swap 1 3

theorem standardZ_normalizes :
    standardZ ∈ normalizer (standardNine : Set (Equiv.Perm (Fin 6))) := by
  rw [mem_normalizer_iff]
  intro x
  change (∃ i, nineEmbedding i = x) ↔ ∃ i, nineEmbedding i = standardZ * x * standardZ⁻¹
  have hc : ∀ i : NineCoordinates, ∃ j : NineCoordinates,
      nineEmbedding j = standardZ * nineEmbedding i * standardZ⁻¹ := by decide +kernel
  constructor
  · rintro ⟨i, rfl⟩
    exact hc i
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hc i
    refine ⟨j, ?_⟩
    rw [hi] at hj
    have hs : standardZ * standardZ = 1 := by decide +kernel
    have hsi : standardZ⁻¹ = standardZ := inv_eq_of_mul_eq_one_right hs
    simpa only [hsi, mul_assoc, ← mul_assoc standardZ standardZ, hs, one_mul,
      mul_one] using hj

def standardMarking : Marking where
  D := standardNine
  card_D := card_standardNine
  z := standardZ
  u := standardU
  z_swap := ⟨0, 2, by decide, rfl⟩
  u_swap := ⟨1, 3, by decide, rfl⟩
  commute := by change standardU * standardZ = standardZ * standardU; decide +kernel
  z_normalizes := standardZ_normalizes
  b_inverts := by
    rintro _ ⟨i, rfl⟩
    have h : ∀ i : NineCoordinates, (standardU * standardZ) * nineEmbedding i *
        (standardU * standardZ)⁻¹ = (nineEmbedding i)⁻¹ := by decide +kernel
    exact h i

end AlternatingSix.M10.LocalGeometry
