module

public import Theory.Representation.BinaryConjugationSection
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Abel

/-!
# Correcting involution lifts through a free binary section

Suppose A/B is a binary module for H and i and x are square-one elements
of H with x i⁻¹ in A. If every i-fixed vector is a displacement, conjugating
x by an element of A makes x i⁻¹ lie in B. Indeed, the coordinates of x i⁻¹
are fixed by i; a lift of a displacement preimage supplies the conjugator.
Normality is relative to H, and the result retains the element of A.

Application: the successive Q/U and U/Z lifting steps in Aschbacher–Smith,
J.2.6, printed p.435 (PDF p.446 of `refs/quasithin.pdf`).
-/

public section
open Subgroup Representation
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H A B : Subgroup G}
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W}

/-- Vanishing first cohomology corrects a square-one lift modulo the section kernel. -/
theorem correct_involution_mod_kernel (d : BinaryConjugationSection H A B ρ)
    (i x : H) (hi : (i : G) ^ 2 = 1) (hx : (x : G) ^ 2 = 1)
    (hfree : ∀ v : W, ρ i v = v → ∃ w : W, ρ i w + w = v)
    (hdiff : (x : G) * (i : G)⁻¹ ∈ A) :
    ∃ a : A, ((a : G) * (x : G) * (a : G)⁻¹) * (i : G)⁻¹ ∈ B := by
  have hneg (v : W) : -v = v := by
    have hh : v + v = 0 := by
      rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2),
        ZMod.natCast_self, zero_smul]
    exact neg_eq_of_add_eq_zero_left hh
  have hxi : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  let c : A := ⟨(x : G) * (i : G)⁻¹, hdiff⟩
  let ic : A := ⟨(i : G) * (c : G) * (i : G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized i.property) c).mp c.property⟩
  have hic : ic = c⁻¹ := by
    apply Subtype.ext
    change (i : G) * ((x : G) * (i : G)⁻¹) * (i : G)⁻¹ =
      ((x : G) * (i : G)⁻¹)⁻¹
    simp only [mul_inv_rev, inv_inv, hxi]
    calc
      _ = (i : G) * x * ((i : G) ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = _ := by rw [hi, inv_one, mul_one]
  have hfix : ρ i (d.coordinates c).toAdd = (d.coordinates c).toAdd := by
    rw [← d.equivariant i c]
    change (d.coordinates ic).toAdd = _
    rw [hic, map_inv]
    exact hneg _
  obtain ⟨w, hw⟩ := hfree _ hfix
  obtain ⟨a, ha⟩ := d.onto (Multiplicative.ofAdd w)
  let ia : A := ⟨(i : G) * (a : G) * (i : G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized i.property) a).mp a.property⟩
  have hia : (d.coordinates ia).toAdd = ρ i w := by
    rw [d.equivariant i a, ha]
    rfl
  have he : (a * c * ia⁻¹ : A) ∈ d.coordinates.ker := by
    change d.coordinates (a * c * ia⁻¹) = 1
    apply Multiplicative.toAdd.injective
    simp only [map_mul, map_inv]
    change (d.coordinates a).toAdd + (d.coordinates c).toAdd +
      -(d.coordinates ia).toAdd = 0
    rw [ha, hia, hneg, ← hw]
    change w + (ρ i w + w) + ρ i w = 0
    have hh (v : W) : v + v = 0 := by
      calc v + v = v + -v := congrArg (v + ·) (hneg v).symm
           _ = 0 := add_neg_cancel v
    calc
      _ = (w + w) + (ρ i w + ρ i w) := by abel
      _ = 0 := by rw [hh, hh, zero_add]
  have hb : ((a * c * ia⁻¹ : A) : G) ∈ B :=
    (d.coordinates_eq_one_iff _).mp he
  refine ⟨a, ?_⟩
  convert hb using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, c, ia]
  group
end Representation.BinaryConjugationSection
