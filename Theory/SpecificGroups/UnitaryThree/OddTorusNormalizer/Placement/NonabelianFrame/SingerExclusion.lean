module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.LinearMaps

/-!
# The characteristic-two cubic exclusion

An involution in characteristic two has square-zero displacement. In degree
three that displacement has rank at most one. The difference between an
operator and its involutory conjugate therefore has rank at most two. If the
involution normalizes an irreducible abelian subgroup, this difference commutes
with that subgroup, and Schur's lemma makes it zero. The involution then also
commutes with the subgroup, so its square-zero displacement is zero.

The final application excludes an irreducible abelian normal subgroup of the
actual special-unitary join H⟨t⟩. Normality is relative to that join. This is
the cubic/Singer exclusion needed while constructing the frame in GLS4,
Chapter 4, Lemma 3.11(a), `refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
-/

open Representation
open scoped IsMulCommutative

public section

namespace UnitaryThree.OddTorusNormalizer.NonabelianFrame

private theorem square_zero_rank_le_one
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hdim : Module.finrank F V = 3)
    (f : Module.End F V) (hf : f * f = 0) :
    Module.finrank F (LinearMap.range f) ≤ 1 := by
  have hle : LinearMap.range f ≤ LinearMap.ker f := LinearMap.range_le_ker_iff.mpr hf
  have hm := Submodule.finrank_mono hle
  have he := f.finrank_range_add_finrank_ker
  omega

/-- In characteristic two an involution normalizing an irreducible abelian
subgroup in a faithful degree-three action is the identity. -/
theorem involution_eq_one_of_irreducible_abelian
    {F G V : Type*} [Field F] [CharP F 2] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank F V = 3) (A : Subgroup G) [IsMulCommutative A]
    [IsIrreducible (ρ.comp A.subtype)]
    (t : G) (ht : t ^ 2 = 1) (htA : t ∈ Subgroup.normalizer A) : t = 1 := by
  have htt : t * t = 1 := by simpa only [pow_two] using ht
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hT : ρ t * ρ t = 1 := by rw [← map_mul, htt, map_one]
  let N : Module.End F V := ρ t - 1
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hadd (f : Module.End F V) : f + f = 0 := by
    rw [← two_smul F f, htwo, zero_smul]
  have hN : N * N = 0 := by
    change (ρ t - 1) * (ρ t - 1) = 0
    calc
      _ = (ρ t * ρ t + 1) - (ρ t + ρ t) := by
        rw [sub_mul, mul_sub, one_mul, mul_one]
        abel
      _ = 0 := by rw [hT, hadd, hadd, sub_zero]
  have hrN := square_zero_rank_le_one hdim N hN
  have hcomm (a b : A) : ρ a.val * ρ b.val = ρ b.val * ρ a.val := by
    rw [← map_mul, ← map_mul]
    exact congrArg (fun x : A => ρ x.val) (mul_comm a b)
  have htcomm (a : A) : ρ t * ρ a.val = ρ a.val * ρ t := by
    let b : A := ⟨t * a.val * t, by
      simpa only [hti] using (Subgroup.mem_normalizer_iff.mp htA a.val).mp a.property⟩
    let d : Module.End F V := ρ a.val - ρ b.val
    have hdcomm (c : A) : d * ρ c.val = ρ c.val * d := by
      dsimp [d]
      rw [sub_mul, mul_sub, hcomm a c, hcomm b c]
    have hbt : ρ b.val * ρ t = ρ t * ρ a.val := by
      change ρ (t * a.val * t) * ρ t = _
      rw [← map_mul]
      have he : t * a.val * t * t = t * a.val := by rw [mul_assoc, htt, mul_one]
      rw [he, map_mul]
    have hd : d = ρ b.val * N - N * ρ a.val := by
      dsimp [d, N]
      rw [mul_sub, sub_mul, mul_one, one_mul, hbt]
      abel
    have hrd : Module.finrank F (LinearMap.range d) ≤ 2 := by
      have hle : LinearMap.range d ≤
          LinearMap.range (ρ b.val * N) ⊔ LinearMap.range N := by
        rintro v ⟨w, rfl⟩
        rw [hd, LinearMap.sub_apply]
        apply Submodule.sub_mem
        · exact Submodule.mem_sup_left (LinearMap.mem_range_self _ w)
        · exact Submodule.mem_sup_right (LinearMap.mem_range_self N (ρ a.val w))
      have hleft : Module.finrank F (LinearMap.range (ρ b.val * N)) ≤ 1 := by
        change Module.finrank F (LinearMap.range ((ρ b.val).comp N)) ≤ 1
        rw [LinearMap.range_comp]
        exact (Submodule.finrank_map_le _ _).trans hrN
      have hsum := Submodule.finrank_add_le_finrank_add_finrank
        (LinearMap.range (ρ b.val * N)) (LinearMap.range N)
      have hmono := Submodule.finrank_mono hle
      omega
    let e : IntertwiningMap (ρ.comp A.subtype) (ρ.comp A.subtype) :=
      ⟨d, fun c => hdcomm c⟩
    have hd0 : d = 0 := by
      rcases IsIrreducible.injective_or_eq_zero e with hi | hz
      · have he := LinearMap.finrank_range_of_inj (show Function.Injective d from hi)
        omega
      · exact congrArg IntertwiningMap.toLinearMap hz
    have heq : ρ a.val = ρ t * ρ a.val * ρ t := by
      simpa only [d, b, map_mul] using sub_eq_zero.mp hd0
    calc
      ρ t * ρ a.val = ρ t * (ρ t * ρ a.val * ρ t) := congrArg (ρ t * ·) heq
      _ = ρ a.val * ρ t := by rw [← mul_assoc, ← mul_assoc, hT, one_mul]
  let e : IntertwiningMap (ρ.comp A.subtype) (ρ.comp A.subtype) :=
    ⟨N, fun a => by
      change (ρ t - 1) * ρ a.val = ρ a.val * (ρ t - 1)
      rw [sub_mul, mul_sub, one_mul, mul_one, htcomm a]⟩
  have hN0 : N = 0 := by
    rcases IsIrreducible.injective_or_eq_zero e with hi | hz
    · apply LinearMap.ext
      intro v
      apply hi
      change (N * N) v = N 0
      rw [hN]
      simp
    · exact congrArg IntertwiningMap.toLinearMap hz
  apply hfaith
  simpa only [map_one] using sub_eq_zero.mp hN0

/-- A genuine special-unitary involution cannot normalize an abelian subgroup
whose action on the natural three-space is irreducible. -/
theorem not_irreducible_abelian_of_involution
    {E : Type*} [Field E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (A : Subgroup J.specialSubgroup) [IsMulCommutative A]
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htA : t ∈ Subgroup.normalizer A) :
    ¬ IsIrreducible ((naturalRepresentation J).comp A.subtype) := by
  intro hi
  let : IsIrreducible ((naturalRepresentation J).comp A.subtype) := hi
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have he := involution_eq_one_of_irreducible_abelian
    (naturalRepresentation J) (naturalRepresentation_injective J) (by simp) A t ht2 htA
  simp [he] at ht

/-- The actual join in Lemma 3.11 cannot have an irreducible abelian normal
subgroup. This uses the given involution and relative normality only. -/
theorem not_irreducible_abelian_normal_in_join
    {E : Type*} [Field E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (H A : Subgroup J.specialSubgroup) [IsMulCommutative A]
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (hA : A ≤ H ⊔ Subgroup.zpowers t)
    (hnormal : (A.subgroupOf (H ⊔ Subgroup.zpowers t)).Normal) :
    ¬ IsIrreducible ((naturalRepresentation J).comp A.subtype) := by
  apply not_irreducible_abelian_of_involution J A t ht
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mp hnormal
  exact (show Subgroup.zpowers t ≤ H ⊔ Subgroup.zpowers t from le_sup_right)
    (Subgroup.mem_zpowers t)

/-- The characteristic hypothesis of the cubic exclusion is supplied by the
literal field cardinality in the even-unitary source. -/
theorem not_irreducible_abelian_normal_in_join_of_card
    {E : Type*} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (n : ℕ) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (H A : Subgroup J.specialSubgroup) [IsMulCommutative A]
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (hA : A ≤ H ⊔ Subgroup.zpowers t)
    (hnormal : (A.subgroupOf (H ⊔ Subgroup.zpowers t)).Normal) :
    ¬ IsIrreducible ((naturalRepresentation J).comp A.subtype) := by
  let : CharP E 2 := charTwo_of_card n hcard
  exact not_irreducible_abelian_normal_in_join J H A t ht hA hnormal

end UnitaryThree.OddTorusNormalizer.NonabelianFrame
