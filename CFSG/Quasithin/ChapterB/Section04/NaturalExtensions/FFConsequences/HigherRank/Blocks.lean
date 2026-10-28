module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import Mathlib.LinearAlgebra.Projection

/-!
# Actual linear blocks of a two-factor extension

Choose an ordinary linear section of the literal quotient map. Its failure
to intertwine is the off-diagonal block. The block is a bimodule derivation,
and zero products of factor and off-diagonal displacements give zero products
on the original representation. No invariant complement is assumed.

This supplies the extension-to-matrix step for the higher-rank branch of
Aschbacher–Smith B.4.9(2)(i), printed pp.92–95.
-/

@[expose] public section
open Representation
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
variable {G V X Y : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  {ρ : Representation (ZMod 2) G V}
  {σ : Representation (ZMod 2) G X} {τ : Representation (ZMod 2) G Y}

/-- Ordinary linear coordinates on an extension, retaining both factor actions. -/
structure ExtensionBlocks (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G X) (τ : Representation (ZMod 2) G Y) where
  inclusion : X →ₗ[ZMod 2] V
  sectionMap : Y →ₗ[ZMod 2] V
  block : G → Y →ₗ[ZMod 2] X
  spanning : ∀ v, ∃ x y, v = inclusion x + sectionMap y
  on_inclusion : ∀ g x, ρ g (inclusion x) = inclusion (σ g x)
  on_section : ∀ g y, ρ g (sectionMap y) = inclusion (block g y) + sectionMap (τ g y)
  derivation : ∀ g h, block (g * h) = (σ g).comp (block h) + (block g).comp (τ h)

/-- Every pair of literal equivariant factor identifications has ordinary
extension blocks, by taking a linear section of the original quotient. -/
theorem exists_extensionBlocks (N : Subrepresentation ρ)
    (en : N.toRepresentation.Equiv σ) (eq : N.quotientRepresentation.Equiv τ) :
    Nonempty (ExtensionBlocks ρ σ τ) := by
  let i : X →ₗ[ZMod 2] V := N.toSubmodule.subtype.comp en.symm.toLinearEquiv.toLinearMap
  let q : V →ₗ[ZMod 2] Y := eq.toLinearEquiv.toLinearMap.comp N.toSubmodule.mkQ
  have hi : Function.Injective i := Subtype.val_injective.comp en.symm.toLinearEquiv.injective
  have hq : Function.Surjective q := eq.toLinearEquiv.surjective.comp N.toSubmodule.mkQ_surjective
  have hi_equiv (g : G) (w : X) : ρ g (i w) = i (σ g w) := by
    exact (congrArg Subtype.val (LinearMap.congr_fun (en.symm.isIntertwining' g) w)).symm
  have hq_equiv (g : G) (v : V) : q (ρ g v) = τ g (q v) := by
    exact LinearMap.congr_fun (eq.isIntertwining' g) (N.toSubmodule.mkQ v)
  have hqker (v : V) : q v = 0 ↔ v ∈ N.toSubmodule := by
    change eq.toLinearEquiv (N.toSubmodule.mkQ v) = 0 ↔ _
    rw [eq.toLinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  obtain ⟨j, hj⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqj (w : Y) : q (j w) = w := LinearMap.congr_fun hj w
  let δ (g : G) : Y →ₗ[ZMod 2] V := (ρ g).comp j - j.comp (τ g)
  have hδ (g : G) (w : Y) : δ g w ∈ N.toSubmodule := by
    apply (hqker _).mp
    change q (ρ g (j w) - j (τ g w)) = 0
    rw [map_sub, hq_equiv, hqj, hqj, sub_self]
  let c (g : G) : Y →ₗ[ZMod 2] X :=
    en.toLinearEquiv.toLinearMap.comp ((δ g).codRestrict N.toSubmodule (hδ g))
  have hic (g : G) (w : Y) : i (c g w) = ρ g (j w) - j (τ g w) := by
    change (en.symm (en ⟨δ g w, hδ g w⟩)).val = _
    rw [en.symm_apply_apply]
    rfl
  refine ⟨{
    inclusion := i
    sectionMap := j
    block := c
    spanning := ?_
    on_inclusion := hi_equiv
    on_section := ?_
    derivation := ?_ }⟩
  · intro v
    have hn : v - j (q v) ∈ N.toSubmodule := by
      apply (hqker _).mp
      rw [map_sub, hqj, sub_self]
    refine ⟨en ⟨v - j (q v), hn⟩, q v, ?_⟩
    change v = (en.symm (en ⟨v - j (q v), hn⟩)).val + j (q v)
    rw [en.symm_apply_apply]
    exact (sub_add_cancel _ _).symm
  · intro g w
    rw [hic, sub_add_cancel]
  · intro g h
    ext w
    apply hi
    change i (c (g * h) w) = i (σ g (c h w) + c g (τ h w))
    rw [hic, map_add, ← hi_equiv, hic, hic, map_sub,
      map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    abel

/-- Vanishing of the three block products is vanishing on the original
module. This is the step that upgrades a coefficient calculation to quadraticity. -/
theorem ExtensionBlocks.displacement_product (b : ExtensionBlocks ρ σ τ) (g h : G)
    (hσ : (σ g - 1) * (σ h - 1) = 0)
    (hτ : (τ g - 1) * (τ h - 1) = 0)
    (hc : (σ g - 1).comp (b.block h) + (b.block g).comp (τ h - 1) = 0) :
    (ρ g - 1) * (ρ h - 1) = 0 := by
  have hi (a : G) (x : X) : (ρ a - 1) (b.inclusion x) = b.inclusion ((σ a - 1) x) := by
    change ρ a (b.inclusion x) - b.inclusion x = b.inclusion (σ a x - x)
    rw [b.on_inclusion, map_sub]
  have hj (a : G) (y : Y) : (ρ a - 1) (b.sectionMap y) =
      b.inclusion (b.block a y) + b.sectionMap ((τ a - 1) y) := by
    change ρ a (b.sectionMap y) - b.sectionMap y =
      b.inclusion (b.block a y) + b.sectionMap (τ a y - y)
    rw [b.on_section, map_sub]
    abel
  ext v
  obtain ⟨x, y, rfl⟩ := b.spanning v
  change (ρ g - 1) ((ρ h - 1) (b.inclusion x + b.sectionMap y)) = 0
  rw [map_add, hi, hj, map_add, hi, map_add, hi, hj]
  have hσx : (σ g - 1) ((σ h - 1) x) = 0 := LinearMap.congr_fun hσ x
  have hτy : (τ g - 1) ((τ h - 1) y) = 0 := LinearMap.congr_fun hτ y
  have hcy : (σ g - 1) (b.block h y) + b.block g ((τ h - 1) y) = 0 :=
    LinearMap.congr_fun hc y
  rw [hσx, hτy, map_zero, map_zero, add_zero, zero_add, ← map_add, hcy, map_zero]
end CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
