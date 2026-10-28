module

public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

/-!
# Residuals and centralizers through central prime-to-p kernels

A commutator into a central p'-kernel is a homomorphism. A p-generated
subgroup kills this homomorphism, so its full centralizer is the inverse
image of the centralizer of its image. For a split central extension, the
projection onto the kernel kills the prime-to-p residual; p-generation of
the section gives the reverse containment.

These arguments include nonperfect p-generated groups, in particular SL₂(3).
They supply the literal centralizer and root-residual transports in
Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17, p.39.
-/

public section
open Subgroup
open scoped commutatorElement

namespace Subgroup

/-- Centralizers of p-generated subgroups lift through a central p'-kernel. -/
theorem comap_centralizer_map_eq_of_primeToResidual
    {G H : Type*} [Group G] [Group H] (p : ℕ)
    (f : G →* H) (hcentral : f.ker ≤ center G)
    (hcop : Nat.Coprime p (Nat.card f.ker))
    (K : Subgroup G) (hK : primeToResidual p K = ⊤) :
    (centralizer (K.map f : Set H)).comap f = centralizer (K : Set G) := by
  apply le_antisymm
  · intro x hx
    have hm (y : K) : ⁅x, (y : G)⁆ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((mem_centralizer_iff.mp hx (f y) (mem_map_of_mem f y.property)).symm)
    let d : K →* f.ker := {
      toFun y := ⟨⁅x, (y : G)⁆, hm y⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro y z
        apply Subtype.ext
        change ⁅x, (y : G) * (z : G)⁆ = ⁅x, (y : G)⁆ * ⁅x, (z : G)⁆
        rw [commutatorElement_mul_right_eq_mul_conj,
          mul_assoc, mul_assoc, ← mul_assoc (y : G),
          mem_center_iff.mp (hcentral (hm z)) (y : G), mul_inv_cancel_right] }
    have hd : ∀ y, d y = 1 := by
      intro y
      exact (primeToResidual_le_ker d hcop) (hK ▸ mem_top y)
    apply mem_centralizer_iff.mpr
    intro y hy
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (congrArg Subtype.val (hd ⟨y, hy⟩))).symm
  · intro x hx
    apply mem_centralizer_iff.mpr
    rintro y ⟨k, hk, rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx k hk)

/-- The residual of a central split extension with p'-kernel is the section image
when the base is p-generated. The section belongs to the prescribed projection. -/
theorem primeToResidual_eq_range_of_central_section
    {G H : Type*} [Group G] [Group H] (p : ℕ)
    (f : G →* H) (hcentral : f.ker ≤ center G)
    (hcop : Nat.Coprime p (Nat.card f.ker))
    (s : H →* G) (hs : f.comp s = MonoidHom.id H)
    (hgen : ∀ h, s h ∈ primeToResidual p G) :
    primeToResidual p G = s.range := by
  have hfs (y : H) : f (s y) = y := DFunLike.congr_fun hs y
  have hk (x : G) : x * (s (f x))⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfs, mul_inv_cancel]
  let d : G →* f.ker := {
    toFun x := ⟨x * (s (f x))⁻¹, hk x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change x * y * (s (f (x * y)))⁻¹ =
        (x * (s (f x))⁻¹) * (y * (s (f y))⁻¹)
      rw [map_mul, map_mul, mul_inv_rev]
      calc
        _ = x * ((y * (s (f y))⁻¹) * (s (f x))⁻¹) := by group
        _ = x * ((s (f x))⁻¹ * (y * (s (f y))⁻¹)) := by
          rw [mem_center_iff.mp (hcentral (hk y)) (s (f x))⁻¹]
        _ = _ := by group }
  apply le_antisymm
  · intro x hx
    have he : x * (s (f x))⁻¹ = 1 :=
      congrArg Subtype.val (show d x = 1 from (primeToResidual_le_ker d hcop) hx)
    exact ⟨f x, (mul_inv_eq_one.mp he).symm⟩
  · rintro x ⟨y, rfl⟩
    exact hgen y

end Subgroup
