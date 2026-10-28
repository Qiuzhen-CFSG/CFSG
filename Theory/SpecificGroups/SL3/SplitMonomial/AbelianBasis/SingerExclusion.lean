module

public import Theory.Representation.GeneralLinearNatural
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Determinant
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Mathlib.GroupTheory.Sylow

/-!
# Excluding the irreducible abelian alternative

Let an involution t normalize an abelian subgroup A acting irreducibly in
SL₃. For a in A, the difference between a and its t-conjugate commutes with A
and is negated by conjugation by t. Its determinant is therefore its own
negative, so it vanishes in characteristic different from two. Schur's lemma
forces the difference to be zero. Thus t centralizes A; applying Schur again
to t - 1 and using determinant one forces t = 1.

A full ambient Sylow two-subgroup contains an involution, since SL₃ contains
`diag(-1,-1,1)`. It consequently cannot normalize an irreducible abelian
subgroup. This excludes the cubic Singer alternative without extending the
coefficient field or constructing its normalizer.

Source: the exclusion of case (c) in the solvable portion of GLS3,
Theorem 6.5.3, `refs/KGroup/GLS3/chapter6.tex`; Aschbacher–Smith,
proof of Proposition 1.3.4, printed p.511 (PDF p.528).
-/

open Representation
open scoped IsMulCommutative
namespace Matrix.SL3.SplitMonomial.AbelianBasis
variable {F : Type*} [Field F]

private theorem commuting_end_eq_zero_of_det_eq_zero
    (A : Subgroup (SpecialLinearGroup (Fin 3) F))
    [IsIrreducible ((specialLinearNatural (k := F) 3).comp A.subtype)]
    (f : Module.End F (Fin 3 → F))
    (hc : ∀ a : A, f * specialLinearNatural 3 a.val = specialLinearNatural 3 a.val * f)
    (hd : f.det = 0) : f = 0 := by
  let e : IntertwiningMap ((specialLinearNatural (k := F) 3).comp A.subtype)
      ((specialLinearNatural (k := F) 3).comp A.subtype) :=
    ⟨f, fun a => hc a⟩
  rcases IsIrreducible.injective_or_eq_zero e with hi | hz
  · exact ((LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd)
      (LinearMap.ker_eq_bot.mpr hi)).elim
  · exact congrArg IntertwiningMap.toLinearMap hz

/-- An involution normalizing an irreducible abelian subgroup of SL₃ is trivial.
The odd-dimensional determinant forces the conjugation differences to vanish. -/
public theorem involution_eq_one_of_normalizes_irreducible_abelian
    (h2 : (2 : F) ≠ 0) (A : Subgroup (SpecialLinearGroup (Fin 3) F))
    [IsMulCommutative A]
    [IsIrreducible ((specialLinearNatural (k := F) 3).comp A.subtype)]
    (t : SpecialLinearGroup (Fin 3) F) (ht : t ^ 2 = 1)
    (htA : t ∈ Subgroup.normalizer (A : Set (SpecialLinearGroup (Fin 3) F))) :
    t = 1 := by
  let ρ := specialLinearNatural (k := F) 3
  have htt : t * t = 1 := by simpa only [pow_two] using ht
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hcomm (a b : A) : ρ a.val * ρ b.val = ρ b.val * ρ a.val := by
    rw [← map_mul, ← map_mul]
    exact congrArg (fun x : A => ρ x.val) (mul_comm a b)
  have htcomm (a : A) : ρ t * ρ a.val = ρ a.val * ρ t := by
    let b : A := ⟨t * a.val * t, by
      simpa only [hti] using (Subgroup.mem_normalizer_iff.mp htA a.val).mp a.property⟩
    let d : Module.End F (Fin 3 → F) := ρ a.val - ρ b.val
    have hdcomm (c : A) : d * ρ c.val = ρ c.val * d := by
      dsimp [d]
      rw [sub_mul, mul_sub, hcomm a c, hcomm b c]
    have htd : ρ t * d * ρ t = -d := by
      dsimp [d, b]
      simp only [mul_sub, sub_mul, ← map_mul]
      have htata : t * (t * a.val * t) * t = a.val := by
        calc
          t * (t * a.val * t) * t = (t * t) * a.val * (t * t) := by group
          _ = a.val := by rw [htt]; simp
      rw [htata]
      simp only [neg_sub]
    have hdet : d.det = 0 := by
      have hd := congrArg LinearMap.det htd
      have ht_det : (ρ t).det = 1 := by
        change (Matrix.toLin' t.val).det = 1
        rw [LinearMap.det_toLin', t.property]
      have hneg : (-d).det = -d.det := by
        rw [← neg_one_smul F d, LinearMap.det_smul]
        simp [pow_succ]
      simp only [map_mul, ht_det, one_mul, mul_one, hneg] at hd
      have hz : (2 : F) * d.det = 0 := by linear_combination hd
      exact (mul_eq_zero.mp hz).resolve_left h2
    have hd0 : d = 0 := commuting_end_eq_zero_of_det_eq_zero A d hdcomm hdet
    have heq : ρ a.val = ρ t * ρ a.val * ρ t := by
      simpa only [d, b, map_mul] using sub_eq_zero.mp hd0
    calc
      ρ t * ρ a.val = ρ t * (ρ t * ρ a.val * ρ t) := congrArg (ρ t * ·) heq
      _ = ρ a.val * ρ t := by rw [← mul_assoc, ← mul_assoc, ← map_mul, htt, map_one, one_mul]
  let e : IntertwiningMap (ρ.comp A.subtype) (ρ.comp A.subtype) :=
    ⟨ρ t - 1, fun a => by
      change (ρ t - 1) * ρ a.val = ρ a.val * (ρ t - 1)
      rw [sub_mul, mul_sub, one_mul, mul_one, htcomm a]⟩
  rcases IsIrreducible.injective_or_eq_zero e with hi | hz
  · have heq : ρ t = -1 := by
      apply LinearMap.ext
      intro v
      have hprod : (ρ t - 1) * (ρ t + 1) = 0 := by
        rw [sub_mul, mul_add, mul_one, one_mul, ← map_mul, htt, map_one]
        simp [add_comm]
      have hv : e ((ρ t + 1) v) = e 0 := by
        change ((ρ t - 1) * (ρ t + 1)) v = (ρ t - 1) 0
        rw [hprod]
        simp
      have hh := hi hv
      exact eq_neg_of_add_eq_zero_left hh
    have hd := congrArg LinearMap.det heq
    have ht_det : (ρ t).det = 1 := by
      change (Matrix.toLin' t.val).det = 1
      rw [LinearMap.det_toLin', t.property]
    have hneg : (-1 : Module.End F (Fin 3 → F)).det = -1 := by
      rw [← neg_one_smul F (1 : Module.End F (Fin 3 → F)), LinearMap.det_smul]
      simp [pow_succ]
    rw [ht_det, hneg] at hd
    exact (h2 (by linear_combination hd)).elim
  · apply specialLinearNatural_injective 3
    have hh : ρ t - 1 = 0 := congrArg IntertwiningMap.toLinearMap hz
    simpa only [map_one] using sub_eq_zero.mp hh

/-- An abelian subgroup normalized by a full ambient Sylow two-subgroup cannot
act irreducibly on the natural three-dimensional module in odd characteristic. -/
public theorem not_irreducible_of_sylow_two_le_normalizer [Finite F]
    (h2 : (2 : F) ≠ 0) (T : Sylow 2 (SpecialLinearGroup (Fin 3) F))
    (A : Subgroup (SpecialLinearGroup (Fin 3) F)) [IsMulCommutative A]
    (hTA : (T : Subgroup _) ≤ Subgroup.normalizer (A : Set (SpecialLinearGroup (Fin 3) F))) :
    ¬ IsIrreducible ((specialLinearNatural (k := F) 3).comp A.subtype) := by
  intro hi
  let : IsIrreducible ((specialLinearNatural (k := F) 3).comp A.subtype) := hi
  have hd : 2 ∣ Nat.card (SpecialLinearGroup (Fin 3) F) := by
    rw [← standardInvolution_orderOf F h2]
    exact orderOf_dvd_natCard (standardInvolution F)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (T.dvd_card_of_dvd_card hd)
  have ht2 : (t : SpecialLinearGroup (Fin 3) F) ^ 2 = 1 := by
    have hh : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
    exact congrArg (fun x : T => (x : SpecialLinearGroup (Fin 3) F)) hh
  have he : t = 1 := Subtype.ext
    (involution_eq_one_of_normalizes_irreducible_abelian h2 A t.val ht2 (hTA t.property))
  simp [he] at ht

end Matrix.SL3.SplitMonomial.AbelianBasis

