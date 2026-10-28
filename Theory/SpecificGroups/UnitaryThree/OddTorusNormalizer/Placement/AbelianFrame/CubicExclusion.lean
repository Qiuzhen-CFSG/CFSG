module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NoncommRing

/-!
# Excluding an irreducible abelian action in characteristic two

On a three-dimensional space in characteristic two, the displacement of an
involution is square-zero and has rank at most one. For any endomorphism `a`,
the difference `a - t*a*t` has image in the sum of the displacement image and
its `a`-image, so its rank is at most two. If the abelian subgroup acts
irreducibly, this difference is an intertwiner and Schur's lemma makes it
zero. Thus the involution centralizes the subgroup. Its own square-zero
displacement is now an intertwiner, so it too vanishes.

This excludes the irreducible cubic alternative without a splitting-field
assumption, an odd-characteristic determinant argument, or a Singer-normalizer
classification. The special-unitary source application is in `AbelianFrame`.

Source: the abelian branch of GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
-/

public section

open Representation
open scoped IsMulCommutative

namespace UnitaryThree.OddTorusNormalizer.AbelianFrame
variable {E G V : Type*} [Field E] [CharP E 2] [Group G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]

omit [FiniteDimensional E V] in
private theorem square_zero_displacement (u : Module.End E V) (hu : u * u = 1) :
    (u - 1) * (u - 1) = 0 := by
  have htwo : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hneg (x : V) : -x = x := by
    apply neg_eq_iff_add_eq_zero.mpr
    rw [← two_smul E, htwo, zero_smul]
  ext v
  have hv : u (u v) = v := congrArg (fun f : Module.End E V => f v) hu
  change u (u v - v) - (u v - v) = 0
  rw [map_sub, hv]
  simp only [sub_eq_add_neg, hneg]
  have hx (x : V) : x + x = 0 := by rw [← two_smul E, htwo, zero_smul]
  rw [add_assoc, ← add_assoc (u v), hx, zero_add, hx]

private theorem rank_displacement_le_one (hdim : Module.finrank E V = 3)
    (u : Module.End E V) (hu : u * u = 1) :
    Module.finrank E (LinearMap.range (u - 1)) ≤ 1 := by
  have hsq := square_zero_displacement u hu
  have hle : LinearMap.range (u - 1) ≤ LinearMap.ker (u - 1) := by
    rintro _ ⟨v, rfl⟩
    change ((u - 1) * (u - 1)) v = 0
    rw [hsq]
    rfl
  have hr := Submodule.finrank_mono hle
  have he := (u - 1).finrank_range_add_finrank_ker
  rw [hdim] at he
  omega

private theorem difference_not_injective (hdim : Module.finrank E V = 3)
    (u a : Module.End E V) (hu : u * u = 1) :
    ¬ Function.Injective (a - u * a * u) := by
  let N := u - 1
  have hN : Module.finrank E (LinearMap.range N) ≤ 1 :=
    rank_displacement_le_one hdim u hu
  have heq : a - u * a * u = -(N * (a * u)) - a * N := by
    dsimp [N]
    noncomm_ring
  have hle : LinearMap.range (a - u * a * u) ≤
      LinearMap.range N ⊔ (LinearMap.range N).map a := by
    rw [heq]
    rintro _ ⟨v, rfl⟩
    apply Submodule.sub_mem
    · apply Submodule.neg_mem
      exact Submodule.mem_sup_left (LinearMap.mem_range_self N ((a * u) v))
    · exact Submodule.mem_sup_right ⟨N v, LinearMap.mem_range_self N v, rfl⟩
  have hr := Submodule.finrank_mono hle
  have hs := (LinearMap.range N).finrank_add_le_finrank_add_finrank
    ((LinearMap.range N).map a)
  have hm := Submodule.finrank_map_le a (LinearMap.range N)
  intro hi
  rw [LinearMap.finrank_range_of_inj hi, hdim] at hr
  omega

/-- An involution normalizing an irreducible abelian subgroup in a faithful
three-dimensional characteristic-two representation is the identity. -/
theorem involution_eq_one_of_normalizes_irreducible_abelian (ρ : Representation E G V)
    (hf : Function.Injective ρ) (hdim : Module.finrank E V = 3)
    (A : Subgroup G) [IsMulCommutative A] [IsIrreducible (ρ.comp A.subtype)]
    (t : G) (ht : t ^ 2 = 1) (htA : t ∈ Subgroup.normalizer A) : t = 1 := by
  have htt : t * t = 1 := by simpa only [pow_two] using ht
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hut : ρ t * ρ t = 1 := by rw [← map_mul, htt, map_one]
  have hcomm (a b : A) : ρ a.val * ρ b.val = ρ b.val * ρ a.val := by
    rw [← map_mul, ← map_mul]
    exact congrArg (fun x : A => ρ x.val) (mul_comm a b)
  have htcomm (a : A) : ρ t * ρ a.val = ρ a.val * ρ t := by
    let b : A := ⟨t * a.val * t, by
      simpa only [hti] using (Subgroup.mem_normalizer_iff.mp htA a.val).mp a.property⟩
    let d : IntertwiningMap (ρ.comp A.subtype) (ρ.comp A.subtype) :=
      ⟨ρ a.val - ρ b.val, fun c => by
        change (ρ a.val - ρ b.val) * ρ c.val = ρ c.val * (ρ a.val - ρ b.val)
        rw [sub_mul, mul_sub, hcomm a c, hcomm b c]⟩
    have hd0 : d = 0 := by
      rcases IsIrreducible.injective_or_eq_zero d with hi | hz
      · change Function.Injective (ρ a.val - ρ b.val) at hi
        exact (difference_not_injective hdim (ρ t) (ρ a.val) hut
          (by simpa only [b, map_mul] using hi)).elim
      · exact hz
    have heq : ρ a.val = ρ t * ρ a.val * ρ t := by
      have hz := congrArg IntertwiningMap.toLinearMap hd0
      change ρ a.val - ρ b.val = 0 at hz
      exact sub_eq_zero.mp (by simpa only [b, map_mul] using hz)
    calc
      ρ t * ρ a.val = ρ t * (ρ t * ρ a.val * ρ t) := congrArg (ρ t * ·) heq
      _ = ρ a.val * ρ t := by rw [← mul_assoc, ← mul_assoc, hut, one_mul]
  let d : IntertwiningMap (ρ.comp A.subtype) (ρ.comp A.subtype) :=
    ⟨ρ t - 1, fun a => by
      change (ρ t - 1) * ρ a.val = ρ a.val * (ρ t - 1)
      rw [sub_mul, mul_sub, one_mul, mul_one, htcomm a]⟩
  have hd0 : d = 0 := by
    rcases IsIrreducible.injective_or_eq_zero d with hi | hz
    · ext v
      apply hi
      change ((ρ t - 1) * (ρ t - 1)) v = (ρ t - 1) 0
      rw [square_zero_displacement _ hut]
      simp
    · exact hz
  apply hf
  have hz := congrArg IntertwiningMap.toLinearMap hd0
  change ρ t - 1 = 0 at hz
  simpa only [map_one] using sub_eq_zero.mp hz
end UnitaryThree.OddTorusNormalizer.AbelianFrame
