module

public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Fixed images through a prime-free kernel

A finite fiber of an equivariant homomorphism has the cardinality of its
kernel. If a p-group fixes its image and p does not divide that cardinality,
orbit counting supplies a fixed representative. Applying this directly to
conjugation gives the full image of a p-subgroup centralizer, without any
normality assumption on the p-subgroup or splitting of the extension.

The argument generalizes the two-group fiber proof in
`Theory.GroupAction.TwoGroupFixedImage` and is used for the cubic centralizers
in Aschbacher–Smith 15.3.60–61, printed p.1150.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

private def kernelEquivFiber (f : G →* H) (x : G) : f.ker ≃ {z : G // f z = f x} where
  toFun n := ⟨x * n, by simp [f.mem_ker.mp n.property]⟩
  invFun z := ⟨x⁻¹ * z, by simp [MonoidHom.mem_ker, z.property]⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- A prime-subgroup centralizer maps onto its image centralizer through a prime-free kernel. -/
lemma centralizer_map_of_prime_free_kernel [Finite G]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : ¬ p ∣ Nat.card f.ker) (D : Subgroup G) (hD : IsPGroup p D) :
    (centralizer (D : Set G)).map f = centralizer (D.map f : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ f)
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  have hcom (d : D) : f d * f x = f x * f d :=
    mem_centralizer_iff.mp hy (f d) (mem_map_of_mem f d.property)
  let Fiber := {z : G // f z = f x}
  have hcard : ¬ p ∣ Nat.card Fiber := by
    rwa [Nat.card_congr (kernelEquivFiber f x).symm]
  let : MulAction D Fiber := {
    smul d z := ⟨(d : G) * z.val * (d : G)⁻¹, by
      rw [map_mul, map_mul, map_inv, z.property,
        hcom d,
        mul_inv_cancel_right]⟩
    one_smul z := Subtype.ext (by
      change (1 : G) * z.val * (1 : G)⁻¹ = z.val
      simp only [one_mul, inv_one, mul_one])
    mul_smul a b z := Subtype.ext (by
      change ((a : G) * (b : G)) * z.val * ((a : G) * (b : G))⁻¹ =
        (a : G) * ((b : G) * z.val * (b : G)⁻¹) * (a : G)⁻¹
      simp only [mul_inv_rev, mul_assoc]) }
  obtain ⟨z, hz⟩ := hD.nonempty_fixed_point_of_prime_not_dvd_card Fiber hcard
  refine ⟨z.val, ?_, z.property⟩
  intro d hd
  have he := congrArg Subtype.val (hz (⟨d, hd⟩ : D))
  exact mul_inv_eq_iff_eq_mul.mp he

variable {A : Type*} [Group A]

/-- Fixed points lift through a kernel of order prime to the acting prime. -/
lemma fixed_image_of_prime_free_kernel [Finite G]
    {p : ℕ} [Fact p.Prime]
    [MulDistribMulAction A G] [MulDistribMulAction A H]
    (hA : IsPGroup p A) (f : G →* H) (hker : ¬ p ∣ Nat.card f.ker)
    (hequiv : ∀ a : A, ∀ g : G, f (a • g) = a • f g) :
    (FixedPoints.subgroup A G).map f = f.range ⊓ FixedPoints.subgroup A H := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, fun a => (hequiv a x).symm.trans (congrArg f (hx a))⟩
  · rintro y ⟨⟨x, rfl⟩, hfix⟩
    let Fiber := {z : G // f z = f x}
    have hnot : ¬ p ∣ Nat.card Fiber := by
      rwa [Nat.card_congr (kernelEquivFiber f x).symm]
    let : MulAction A Fiber :=
      { smul := fun a z => ⟨a • z.val, by rw [hequiv, z.property, hfix a]⟩
        one_smul := fun z => Subtype.ext (one_smul A z.val)
        mul_smul := fun a b z => Subtype.ext (mul_smul a b z.val) }
    obtain ⟨z, hz⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card Fiber hnot
    exact ⟨z.val, fun a => congrArg Subtype.val (hz a), z.property⟩

/-- Cardinality of a subgroup containing the kernel, in terms of its actual image. -/
lemma card_subgroup_of_ker_le (f : G →* H) (C : Subgroup G) (hC : f.ker ≤ C) :
    Nat.card C = Nat.card f.ker * Nat.card (C.map f) := by
  have hc := (f.ker.subgroupOf C).card_mul_index
  change Nat.card (f.ker.subgroupOf C) * f.ker.relIndex C = Nat.card C at hc
  rw [relIndex_ker, Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv] at hc
  exact hc.symm


end Subgroup
