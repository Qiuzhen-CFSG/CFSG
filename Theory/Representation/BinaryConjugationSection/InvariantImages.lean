module

public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.Generation
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Invariant images in literal binary sections

An invariant subgroup containing the kernel meets an irreducible section in
either its kernel or its whole numerator. Coordinate membership detects the
original subgroup when it contains the kernel. If a normalizing subgroup
acts through all nonzero scalars of an extension field, its invariant binary
images are field submodules; their dimensions follow from literal indices.

These bridges identify the maximal quotient's seed line and tensor plane in
Aschbacher–Smith, 13.8.30, printed p.964, without assuming those dimensions.
-/

@[expose] public section
namespace Representation.BinaryConjugationSection
open Subgroup
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H A B : Subgroup G} {ρ : Representation (ZMod 2) H W}
  (d : BinaryConjugationSection H A B ρ)

include d in
theorem inf_eq_kernel_of_irreducible [IsIrreducible ρ] (N : Subgroup G) (hN : H ≤ normalizer N)
    (hBN : B ≤ N) (hAN : ¬ A ≤ N) : A ⊓ N = B := by
  let P : Subrepresentation ρ := {
    toSubmodule := d.imageSpace N
    apply_mem_toSubmodule h := by
      intro w hw
      obtain ⟨x,hx,rfl⟩ := (d.mem_imageSpace_iff N w).mp hw
      refine (d.mem_imageSpace_iff N _).mpr ⟨⟨h * x * (h : G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized h.property) x).mp x.property⟩,
        (mem_normalizer_iff.mp (hN h.property) x).mp hx, d.equivariant h x⟩ }
  have hz : P = ⊥ := (eq_bot_or_eq_top P).resolve_right (fun he => by
    apply hAN
    apply (d.le_sup_kernel_of_image_top N
      (congrArg Subrepresentation.toSubmodule he)).trans
    exact sup_le le_rfl hBN)
  apply le_antisymm ?_ (le_inf d.kernel_le hBN)
  intro x hx
  apply (d.coordinates_eq_one_iff ⟨x,hx.1⟩).mp
  have hm : (d.coordinates ⟨x,hx.1⟩).toAdd ∈ P :=
    (d.mem_imageSpace_iff N _).mpr ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  rw [hz] at hm
  exact hm
theorem coordinates_mem_imageSpace_iff_of_kernel_le (N : Subgroup G) (hBN : B ≤ N) (a : A) :
    (d.coordinates a).toAdd ∈ d.imageSpace N ↔ (a : G) ∈ N := by
  constructor
  · intro hm
    obtain ⟨x,hx,he⟩ := (d.mem_imageSpace_iff N _).mp hm
    have hk : ((x⁻¹ * a : A) : G) ∈ B := by
      apply (d.coordinates_eq_one_iff _).mp
      rw [map_mul, map_inv, Multiplicative.toAdd.injective he, inv_mul_cancel]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using
      N.mul_mem hx (hBN hk)
  · intro ha
    exact (d.mem_imageSpace_iff N _).mpr ⟨a,ha,rfl⟩
end Representation.BinaryConjugationSection

namespace Representation.BinaryConjugationSection
open Subgroup
variable {G W F : Type*} [Group G] [Field F]
  [AddCommGroup W] [Module (ZMod 2) W] [Module F W]
  {H S E : Subgroup G} {ρ : Representation (ZMod 2) H W}
  (d : BinaryConjugationSection H S E ρ)

theorem imageSpace_apply_mem (B : Subgroup G) (h : H)
    (hn : (h : G) ∈ normalizer B) (v : W) (hv : v ∈ d.imageSpace B) :
    ρ h v ∈ d.imageSpace B := by
  obtain ⟨x,hx,rfl⟩ := (d.mem_imageSpace_iff B _).mp hv
  exact (d.mem_imageSpace_iff B _).mpr ⟨⟨h * x * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized h.property) x).mp x.property⟩,
    (mem_normalizer_iff.mp hn x).mp hx, d.equivariant h x⟩

variable (X : Subgroup G) (hXH : X ≤ H) (χ : X →* Fˣ)
  (hχ : Function.Surjective χ)
  (hs : ∀ x w, ρ (inclusion hXH x) w = (χ x : F) • w)
  (B : Subgroup G) (hn : X ≤ normalizer B)

def scalarImage : Submodule F W where
  carrier := d.imageSpace B
  zero_mem' := (d.imageSpace B).zero_mem
  add_mem' := (d.imageSpace B).add_mem
  smul_mem' r v hv := by
    by_cases hr : r = 0
    · rw [hr, zero_smul]; exact (d.imageSpace B).zero_mem
    obtain ⟨x,hx⟩ := hχ (Units.mk0 r hr)
    have hh := d.imageSpace_apply_mem B (inclusion hXH x) (hn x.property) v hv
    rw [hs,hx] at hh
    exact hh

theorem scalarImage_card (hB : B ≤ S) :
    Nat.card (d.scalarImage X hXH χ hχ hs B hn) = E.relIndex B :=
  d.imageSpace_card_eq_relIndex B hB

theorem scalarImage_finrank [Finite G] [Finite F] (hF : 1 < Nat.card F)
    (hB : B ≤ S) (n : ℕ) (hi : E.relIndex B = Nat.card F ^ n) :
    Module.finrank F (d.scalarImage X hXH χ hχ hs B hn) = n := by
  let : Finite W := Finite.of_surjective (fun x : S => (d.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  have he := d.scalarImage_card X hXH χ hχ hs B hn hB
  rw [Module.natCard_eq_pow_finrank (K := F), hi] at he
  exact Nat.pow_right_injective hF he
end Representation.BinaryConjugationSection
