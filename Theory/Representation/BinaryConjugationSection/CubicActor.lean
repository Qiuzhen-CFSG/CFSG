module
public import Theory.Representation.BinaryConjugationSection.SL2CubicFixed
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Tactic.Group
/-!
# Cubic actors on central binary sections

A cubic actor trivial on a binary section with central kernel centralizes
its numerator: its displacement has exponent two and is fixed, so both
its square and cube act trivially. Consequently a noncentral cubic actor
on a paired natural section has a cubic coordinate image. This avoids
assuming compatibility between independently marked product quotients.

Source application: Aschbacher–Smith 10.2.3(4), printed p.746, for the
actual odd Hall element in the original paired natural source.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {H W E : Subgroup G} {ρ : Representation (ZMod 2) H V}
  [IsElementaryAbelian 2 W]

/-- A cubic actor trivial modulo a central binary kernel fixes the numerator. -/
theorem centralizes_of_cubic_coordinate_kernel
    (c : BinaryConjugationSection H W E ρ)
    (hE : E ≤ centralizer (H : Set G))
    (b : H) (hb : b ^ 3 = 1) (hρ : ρ b = 1) :
    W ≤ centralizer ({(b:G)} : Set G) := by
  intro a ha x hx
  rw [Set.mem_singleton_iff.mp hx]
  let a₁ : W := ⟨(b:G)*a*(b:G)⁻¹,
    (mem_normalizer_iff.mp (c.normalized b.property) a).mp ha⟩
  let d : W := a₁ * (⟨a,ha⟩ : W)⁻¹
  have hcoords : c.coordinates a₁ = c.coordinates ⟨a,ha⟩ := by
    apply Multiplicative.toAdd.injective
    exact (c.equivariant b ⟨a,ha⟩).trans (by rw [hρ]; rfl)
  have hdE : (d:G) ∈ E := (c.coordinates_eq_one_iff d).mp (by
    change c.coordinates (a₁ * (⟨a,ha⟩ : W)⁻¹) = 1
    rw [map_mul,map_inv,hcoords,mul_inv_cancel])
  have hdb : (b:G)*(d:G)*(b:G)⁻¹ = d := by
    rw [hE hdE b b.property,mul_inv_cancel_right]
  have hd2 : (d:G)^2=1 := by
    exact elemPow_eq_one_of_isElementaryAbelian (d:G) d.property
  have hb2 : (b:G)*((b:G)*a*(b:G)⁻¹)*(b:G)⁻¹ = a := by
    calc
      (b:G)*((b:G)*a*(b:G)⁻¹)*(b:G)⁻¹ =
          ((b:G)*(d:G)*(b:G)⁻¹)*((b:G)*a*(b:G)⁻¹) := by dsimp [d,a₁]; group
      _ = (d:G)*((b:G)*a*(b:G)⁻¹) := by rw [hdb]
      _ = (d:G)*((d:G)*a) := by dsimp [d,a₁]; group
      _ = a := by rw [←mul_assoc,←pow_two,hd2,one_mul]
  have hb3 : (b:G)^3=1 := congrArg H.subtype hb
  have he : (b:G)*a*(b:G)⁻¹ = a := by
    calc
      (b:G)*a*(b:G)⁻¹ =
          (b:G)*((b:G)*((b:G)*a*(b:G)⁻¹)*(b:G)⁻¹)*(b:G)⁻¹ := by rw [hb2]
      _ = (b:G)^3*a*((b:G)^3)⁻¹ := by simp only [pow_succ,pow_zero]; group
      _ = a := by rw [hb3,inv_one,one_mul,mul_one]
  exact (mul_inv_eq_iff_eq_mul).mp he
variable {F : Type*} [Field F] [CharP F 2]
local instance cubicActorFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- A noncentral cubic actor has a cubic image in one of the two marked factors. -/
theorem paired_cubic_image_of_noncentral
    (q₁ q₂ : H →* SL(2,F))
    (c : BinaryConjugationSection H W E
      (Representation.prod (SL2.BinarySmall.natural.comp q₁) (SL2.BinarySmall.natural.comp q₂)))
    (hE : E ≤ centralizer (H : Set G))
    (b : H) (hb : orderOf b=3) (hmove : (b:G) ∉ centralizer (W : Set G)) :
    orderOf (q₁ b)=3 ∨ orderOf (q₂ b)=3 := by
  by_contra! hn
  have hb3 : b^3=1 := by simpa [hb] using pow_orderOf_eq_one b
  have h₁ : q₁ b=1 := by
    by_contra hne
    exact hn.1 (orderOf_eq_prime (by rw [←map_pow,hb3,map_one]) hne)
  have h₂ : q₂ b=1 := by
    by_contra hne
    exact hn.2 (orderOf_eq_prime (by rw [←map_pow,hb3,map_one]) hne)
  have hρ : (Representation.prod (SL2.BinarySmall.natural.comp q₁)
      (SL2.BinarySmall.natural.comp q₂)) b=1 := by
    ext v <;> simp [Representation.prod,h₁,h₂]
  have hf := c.centralizes_of_cubic_coordinate_kernel hE b hb3 hρ
  apply hmove
  intro a ha
  exact (hf ha b (Set.mem_singleton _)).symm
end Representation.BinaryConjugationSection
