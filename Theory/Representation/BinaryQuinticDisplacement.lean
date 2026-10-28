module
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.BinaryOffender.QuadraticImageBound
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# Binary displacement forced by quintic commutators

An order-five commutator moves at least four binary dimensions. The
commutator displacement inequality therefore forces its first actor to
move at least two. In an actual conjugation section, a commutator group
of order at most two gives displacement at most one. Consequently an
elementary actor with quintic involution commutators lies in the actual
section kernel. The source application is the reciprocal core-escape
step for the quintic critical pair in Aschbacher--Smith F.9 and14.2.21.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A commutator of order five forces displacement at least two. -/
theorem two_le_displacement_of_commutator_order_five
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (t x : G) (hx : orderOf (t*x*t⁻¹*x⁻¹) = 5) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) := by
  have hl := prime_order_le_fixedCodim ρ hρ (by decide : Nat.Prime 5)
    (by decide : 5 ≠ 2) (t*x*t⁻¹*x⁻¹) hx
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hl
  have hu := fixedCodim_commutator_le_twice ρ t x
  rw [fixedCodim_zpowers_eq_displacement_rank ρ t] at hu
  omega

/-- The same lower bound on the literal action, with its actual image. -/
theorem two_le_displacement_of_image_commutator_order_five
    (ρ : Representation (ZMod 2) G V) (t x : G)
    (hx : orderOf (actionHom ρ (t*x*t⁻¹*x⁻¹)) = 5) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) := by
  apply two_le_displacement_of_commutator_order_five (imageRepresentation ρ)
    (imageRepresentation_injective ρ) (actionHom ρ t) (actionHom ρ x)
  simpa only [map_mul,map_inv] using hx
end Representation.BinaryOffender

namespace Representation.BinaryConjugationSection
open Subgroup
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}

theorem displacement_le_one_of_commutator_card_two
    (d : BinaryConjugationSection H U Z ρ) (A B : Subgroup G)
    (hAH : A ≤ H) (hc : ⁅A,U⁆ ≤ B) (hB : Nat.card B ≤ 2) (a : H) (ha : (a : G) ∈ A) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1 := by
  let C := B ⊓ U
  have hC : C ≤ U := inf_le_right
  have hcomm : ⁅A,U⁆ ≤ C := le_inf hc
    (le_normalizer_iff_commutator_le_right.mp (hAH.trans d.normalized))
  have hcardC : Nat.card C ≤ 2 := (card_le_of_le inf_le_left).trans hB
  have himg : Nat.card (d.imageSpace C) ≤ 2 := by
    rw [d.imageSpace_card_eq_relIndex C hC]
    exact (Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card Z C)).trans hcardC
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at himg
  have hdim : Module.finrank (ZMod 2) (d.imageSpace C) ≤ 1 := by
    by_contra! hn
    have hh : 4 ≤ 2 ^ Module.finrank (ZMod 2) (d.imageSpace C) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega
  exact (Submodule.finrank_mono
    (d.displacement_range_le_imageSpace_of_commutator_le A C hcomm a ha)).trans hdim

/-- A binary section with quintic involution commutators cannot have a
nontrivial elementary actor whose displacement is confined to an order-two group. -/
theorem elementary_le_actor_kernel_of_commutator_card_two
    {K : Type*} [Group K] [Finite K]
    (σ : Representation (ZMod 2) K W) (hσ : Function.Injective σ)
    (π : H →* K) (d : BinaryConjugationSection H U Z (σ.comp π))
    (hw : ∀ t : K, t ≠ 1 → t ^ 2 = 1 → ∃ x : K, orderOf (t*x*t⁻¹*x⁻¹) = 5)
    (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hAH : A ≤ H) (hc : ⁅A,U⁆ ≤ B) (hB : Nat.card B ≤ 2) :
    A.subgroupOf H ≤ π.ker := by
  intro a ha
  by_contra hn
  have hne : π a ≠ 1 := hn
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (a : G) ha
  have hp2 : (π a) ^ 2 = 1 := by rw [←map_pow,ha2,map_one]
  obtain ⟨x,hx⟩ := hw (π a) hne hp2
  have hl := BinaryOffender.two_le_displacement_of_commutator_order_five σ hσ (π a) x hx
  have hu := d.displacement_le_one_of_commutator_card_two A B hAH hc hB a ha
  change Module.finrank (ZMod 2) (LinearMap.range (σ (π a) - LinearMap.id)) ≤ 1 at hu
  omega
end Representation.BinaryConjugationSection
