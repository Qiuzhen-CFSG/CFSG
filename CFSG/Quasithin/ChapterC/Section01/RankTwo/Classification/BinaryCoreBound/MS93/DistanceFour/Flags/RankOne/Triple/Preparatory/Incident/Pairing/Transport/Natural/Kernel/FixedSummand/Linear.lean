module
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.Abel

/-!
# The cubic-fixed summand of a reflection displacement

For a binary representation of the literal S₃, the cubic norm is a central
projection. It preserves a reflection's displacement image, and that projected
image is fixed by the whole group. Consequently the cubic-fixed part of the
orbit span of the displacement already lies in the original displacement and
is fixed by the full actor. An arbitrary reflection-fixed seed would not have
this property.

This is the linear calculation for Meierfrankenfeld--Stellmacher (1993),
(4.6.8)(3), printed p.906. Its application to the incident seed requires the
actual bar action and its displacement image to be identified separately.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
namespace BinaryS3

abbrev Actor := Equiv.Perm (Fin 3)

def cubic : Actor := Equiv.swap 0 1 * Equiv.swap 1 2

theorem cubic_cube : cubic ^ 3 = 1 := by decide +kernel

private theorem cubic_conjugation : ∀ g : Actor,
    (g * cubic = cubic * g ∧ g * cubic ^ 2 = cubic ^ 2 * g) ∨
    (g * cubic = cubic ^ 2 * g ∧ g * cubic ^ 2 = cubic * g) := by decide +kernel

private theorem reflection_words : ∀ t : Actor, t ^ 2 = 1 → t ≠ 1 →
    ∀ g : Actor, g = 1 ∨ g = cubic ∨ g = cubic ^ 2 ∨
      g = t ∨ g = cubic * t ∨ g = cubic ^ 2 * t := by decide +kernel

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) Actor W)

def norm : W →ₗ[ZMod 2] W := 1 + ρ cubic + ρ (cubic ^ 2)

theorem norm_apply (v : W) : norm ρ v = v + ρ cubic v + ρ (cubic ^ 2) v := rfl

private theorem add_self (v : W) : v + v = 0 := by
  have h := @two_smul (ZMod 2) W _ _ _ v
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_smul] at h
  exact h.symm

theorem norm_of_fixed {v : W} (hv : ρ cubic v = v) : norm ρ v = v := by
  have hv2 : ρ (cubic ^ 2) v = v := by
    rw [pow_two, map_mul, Module.End.mul_apply, hv, hv]
  rw [norm_apply, hv, hv2, add_self, zero_add]

theorem norm_fixed (v : W) : ρ cubic (norm ρ v) = norm ρ v := by
  have h1 : cubic * cubic = cubic ^ 2 := (pow_two _).symm
  have h2 : cubic * cubic ^ 2 = 1 := by rw [← pow_succ', cubic_cube]
  simp only [norm_apply, map_add, ← Module.End.mul_apply, ← map_mul, h1, h2,
    map_one, Module.End.one_apply]
  abel

theorem norm_equivariant (g : Actor) (v : W) : norm ρ (ρ g v) = ρ g (norm ρ v) := by
  rw [norm_apply, norm_apply]
  simp only [map_add, ← Module.End.mul_apply, ← map_mul]
  rcases cubic_conjugation g with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2]
    abel

def displacement (t : Actor) : Submodule (ZMod 2) W := LinearMap.range (ρ t - 1)

def orbitSpan (D : Submodule (ZMod 2) W) : Submodule (ZMod 2) W :=
  ⨆ g : Actor, D.map (ρ g)

private theorem reflection_fixed (t : Actor) (ht : t ^ 2 = 1)
    {v : W} (hv : v ∈ displacement ρ t) : ρ t v = v := by
  obtain ⟨w, rfl⟩ := hv
  have he : ρ t (ρ t w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ht, map_one]
    rfl
  change ρ t (ρ t w - w) = ρ t w - w
  rw [map_sub, he]
  have hn (x : W) : -x = x := neg_eq_iff_add_eq_zero.mpr (add_self x)
  simp only [sub_eq_add_neg, hn]
  abel

theorem norm_mem_displacement (t : Actor) {v : W} (hv : v ∈ displacement ρ t) :
    norm ρ v ∈ displacement ρ t := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨norm ρ w, ?_⟩
  change ρ t (norm ρ w) - norm ρ w = norm ρ (ρ t w - w)
  rw [map_sub, norm_equivariant]

theorem norm_displacement_invariant (t : Actor) (ht : t ^ 2 = 1) (htne : t ≠ 1)
    {v : W} (hv : v ∈ displacement ρ t) : norm ρ v ∈ ρ.invariants := by
  have hc := norm_fixed ρ v
  have hc2 : ρ (cubic ^ 2) (norm ρ v) = norm ρ v := by
    rw [pow_two, map_mul, Module.End.mul_apply, hc, hc]
  have hf := reflection_fixed ρ t ht (norm_mem_displacement ρ t hv)
  intro g
  rcases reflection_words t ht htne g with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact hc
  · exact hc2
  · exact hf
  · rw [map_mul, Module.End.mul_apply, hf, hc]
  · rw [map_mul, Module.End.mul_apply, hf, hc2]

theorem norm_orbitSpan_le (t : Actor) (ht : t ^ 2 = 1) (htne : t ≠ 1) :
    orbitSpan ρ (displacement ρ t) ≤
      (displacement ρ t ⊓ ρ.invariants).comap (norm ρ) := by
  apply iSup_le
  intro g
  rintro _ ⟨v, hv, rfl⟩
  have hf := norm_displacement_invariant ρ t ht htne hv
  change norm ρ (ρ g v) ∈ displacement ρ t ⊓ ρ.invariants
  rw [norm_equivariant, hf g]
  exact ⟨norm_mem_displacement ρ t hv, hf⟩

theorem fixed_orbitSpan (t : Actor) (ht : t ^ 2 = 1) (htne : t ≠ 1)
    {v : W} (hv : v ∈ orbitSpan ρ (displacement ρ t))
    (hfixed : ρ cubic v = v) : v ∈ displacement ρ t ∧ v ∈ ρ.invariants := by
  have h := norm_orbitSpan_le ρ t ht htne hv
  change norm ρ v ∈ displacement ρ t ⊓ ρ.invariants at h
  rwa [norm_of_fixed ρ hfixed] at h

end BinaryS3
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
