module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.FullSquareQuotient
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The full binary G₂ Sylow quotient over its C₄² radical

The normal radical of the second vertex lies in its original common Sylow.
The resulting quotient has order four and injects through the actual vertex
projection into D₁₂. No element of D₁₂ has order four, so this quotient is E₄.
The final equivalence transports the original C₄² kernel, without replacing
the chosen Sylow or assuming an extension shape.

Source: Aschbacher–Smith F.6.18(11), with F.1.12(I)(3)'s marked binary model.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinaryParabolicPair.FullSquare
open BinaryCore ExceptionalLocalQuotients

def sylow : Sylow 2 secondParabolic := commonSylow.subtype commonSylow_le_second

def sylowEquiv : sylow ≃* commonSylow := subgroupOfEquivOfLe commonSylow_le_second

theorem radical_le_sylow : radical ≤ (sylow : Subgroup secondParabolic) :=
  (pCore_isPGroup.map inner.subtype).le_sylow_of_normal sylow

def sylowRadical : Subgroup sylow := radical.subgroupOf (sylow : Subgroup secondParabolic)

instance sylowRadical_normal : sylowRadical.Normal := inferInstanceAs
  (radical.subgroupOf (sylow : Subgroup secondParabolic)).Normal

def sylowRadicalEquiv : sylowRadical ≃* C4Square :=
  (subgroupOfEquivOfLe radical_le_sylow).trans radicalEquiv

theorem sylow_card : Nat.card sylow = 64 := by
  rw [Nat.card_congr sylowEquiv.toEquiv]
  exact card_unipotent_binary

theorem sylowRadical_card : Nat.card sylowRadical = 16 := by
  change Nat.card (radical.subgroupOf (sylow : Subgroup secondParabolic)) = 16
  rw [Nat.card_congr (subgroupOfEquivOfLe radical_le_sylow).toEquiv]
  exact radical_card

theorem sylowQuotient_card : Nat.card (sylow ⧸ sylowRadical) = 4 := by
  have hc := sylowRadical.card_mul_index
  rw [sylowRadical_card,sylow_card] at hc
  change sylowRadical.index = 4
  omega

def projectSylow : sylow →* Q := project.comp (sylow : Subgroup secondParabolic).subtype

theorem projectSylow_ker : projectSylow.ker = sylowRadical := by
  ext x
  change (QuotientGroup.mk (x : secondParabolic) : Q) = 1 ↔
    (x : secondParabolic) ∈ radical
  exact QuotientGroup.eq_one_iff _

def sylowQuotientEquivRange : (sylow ⧸ sylowRadical) ≃* projectSylow.range :=
  (QuotientGroup.quotientMulEquivOfEq projectSylow_ker.symm).trans
    (QuotientGroup.quotientKerEquivRange projectSylow)

def sylowQuotientEmbedding : (sylow ⧸ sylowRadical) →* DihedralGroup 6 :=
  quotientEquiv.toMonoidHom.comp
    (projectSylow.range.subtype.comp sylowQuotientEquivRange.toMonoidHom)

theorem sylowQuotientEmbedding_injective : Function.Injective sylowQuotientEmbedding :=
  quotientEquiv.injective.comp
    (projectSylow.range.subtype_injective.comp sylowQuotientEquivRange.injective)

theorem sylowQuotient_square (x : sylow ⧸ sylowRadical) : x ^ 2 = 1 := by
  have hx4 := pow_card_eq_one' (x := x)
  rw [sylowQuotient_card] at hx4
  have hy4 : sylowQuotientEmbedding x ^ 4 = 1 := by rw [← map_pow,hx4,map_one]
  have hy2 : sylowQuotientEmbedding x ^ 2 = 1 :=
    (by decide : ∀ y : DihedralGroup 6, y ^ 4 = 1 → y ^ 2 = 1) _ hy4
  apply sylowQuotientEmbedding_injective
  simpa only [map_pow,map_one] using hy2

/-- The literal Sylow quotient is the elementary four-group. -/
def sylowQuotientEquiv : (sylow ⧸ sylowRadical) ≃*
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  let X := sylow ⧸ sylowRadical
  let E := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (sylow ⧸ sylowRadical)
    rw [sylowQuotient_card]
    decide)
  let : IsKleinFour X := {
    card_four := sylowQuotient_card
    exponent_two := by
      apply Nat.dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one sylowQuotient_square)
      obtain ⟨x,hx⟩ := exists_ne (1 : X)
      have ho : orderOf x = 2 := orderOf_eq_prime (sylowQuotient_square x) hx
      simpa only [ho] using Monoid.order_dvd_exponent x }
  let : IsKleinFour E := {
    card_four := by simp [E,Nat.card_eq_fintype_card]
    exponent_two := by simp [E,Monoid.exponent_prod] }
  exact IsKleinFour.nonempty_mulEquiv.some

end Atlas.G2.BinaryParabolicPair.FullSquare
