module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.QuadraticBound
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The scalar-cube step in full Levi generation

In the two-dimensional axis group the full Levi centralizer acts on a
second parameter by a • e + t³ • x. Polarization of cubes shows that their
additive span is the whole defining field except F₄. Consequently these
affine cubic orbits generate the additive axis plane. The exceptional
case will instead use every four-group outside a root line.

Source: Aschbacher–Smith B.4.9(1), printed p.92, combined manuscript
of 1 March 2004.
-/

public section
open Polynomial
open CFSG.Quasithin.ChapterK.Linear.Natural
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
namespace CubeGeneration
private theorem polarization {K : Type*} [Field K] [CharP K 2] (a : K) :
    (a+1)^3+a^3+1 = a^2+a := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (a^3+a^2+a+1)*h2

private theorem mixed_polarization {K : Type*} [Field K] [CharP K 2] (a b : K) :
    ((a*b)^2+a*b) + b^2*(a^2+a) = a*(b+b^2) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (a*b)^2*h2

private theorem exists_nontrivial_cube (F : BinaryField) (hF : 4 < Nat.card F.Carrier) :
    ∃ t : F.Carrier, t^3 ≠ 0 ∧ t^3 ≠ 1 := by
  classical
  let := Fintype.ofFinite F.Carrier
  by_contra! h
  have hx (x : F.Carrier) : x^4-x = 0 := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [pow_succ, h x (pow_ne_zero _ hx), one_mul, sub_self]
  have hp : (X^4-X : F.Carrier[X]) ≠ 0 := by
    intro he
    have hc := congrArg (fun p : F.Carrier[X] => p.coeff 4) he
    norm_num [Polynomial.coeff_X] at hc
  have hb := Polynomial.card_le_degree_of_subset_roots
    (p := (X^4-X : F.Carrier[X])) (Z := Finset.univ) (by
      intro x _
      exact (Polynomial.mem_roots hp).mpr (by simpa using hx x))
  have hd : (X^4-X : F.Carrier[X]).natDegree ≤ 4 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by norm_num)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hb
  omega

/-- Scalar cubes additively generate every binary defining field except F₄. -/
theorem eq_top_of_cubes (F : BinaryField) (hF : F.degree ≠ 2)
    (S : AddSubgroup F.Carrier) (hc : ∀ t : F.Carrier, t^3 ∈ S) : S = ⊤ := by
  apply top_unique
  intro z _
  by_cases hsmall : F.degree = 1
  · have hs : Function.Surjective (algebraMap (ZMod 2) F.Carrier) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
        ((field_finrank F).trans hsmall)).2
    obtain ⟨c, rfl⟩ := hs z
    fin_cases c
    · change (algebraMap (ZMod 2) F.Carrier) (0 : ZMod 2) ∈ S
      rw [map_zero]
      exact S.zero_mem
    · change (algebraMap (ZMod 2) F.Carrier) (1 : ZMod 2) ∈ S
      rw [map_one]
      simpa using hc 1
  · have hcard : 4 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have hd := F.degree_pos
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 2 < F.degree)
    obtain ⟨t, ht0, ht1⟩ := exists_nontrivial_cube F hcard
    let b := t^3
    have hb : b+b^2 ≠ 0 := by
      rw [pow_two, ← mul_one_add]
      exact mul_ne_zero ht0 (by
        intro hh
        apply ht1
        have hz := eq_neg_of_add_eq_zero_right hh
        simpa only [CharTwo.neg_eq] using hz)
    have hp (a : F.Carrier) : a^2+a ∈ S := by
      rw [← polarization a]
      exact S.add_mem (S.add_mem (hc _) (hc _)) (by simpa using hc 1)
    have hscaled (a : F.Carrier) : b^2 * (a^2+a) ∈ S := by
      have hid : b^2 * (a^2+a) =
          (t^2*(a+1))^3 + (t^2*a)^3 + (t^2)^3 := by
        rw [mul_pow, mul_pow, ← mul_add, ← mul_add_one, polarization]
        simp only [b, ← pow_mul]
      rw [hid]
      exact S.add_mem (S.add_mem (hc _) (hc _)) (hc _)
    have hall (a : F.Carrier) : a*(b+b^2) ∈ S := by
      rw [← mixed_polarization]
      exact S.add_mem (hp (a*b)) (hscaled a)
    have hz := hall (z/(b+b^2))
    rwa [div_mul_cancel₀ _ hb] at hz

/-- The actual additive calculation for the determinant-twisted GL₂ orbit. -/
theorem eq_top_of_cubic_orbit (F : BinaryField) (hF : F.degree ≠ 2)
    {W : Type*} [AddCommGroup W] [Module F.Carrier W]
    (S : AddSubgroup W) (e x : W)
    (hspan : ∀ w, ∃ a b : F.Carrier, w = a • e + b • x)
    (horbit : ∀ a t : F.Carrier, t ≠ 0 → a • e + t^3 • x ∈ S) : S = ⊤ := by
  have he (a : F.Carrier) : a • e ∈ S := by
    have h := S.sub_mem (horbit a 1 one_ne_zero) (horbit 0 1 one_ne_zero)
    simpa only [one_pow, one_smul, zero_smul, zero_add, add_sub_cancel_right] using h
  let f : F.Carrier →+ W :=
    { toFun := fun c => c • x
      map_zero' := zero_smul _ _
      map_add' := fun a b => add_smul a b x }
  have hs : S.comap f = ⊤ := eq_top_of_cubes F hF (S.comap f) (by
    intro t
    by_cases ht : t = 0
    · simp [ht]
    · change t^3 • x ∈ S
      simpa only [zero_smul, zero_add] using horbit 0 t ht)
  apply top_unique
  intro w _
  obtain ⟨a, b, rfl⟩ := hspan w
  exact S.add_mem (he a) (show b ∈ S.comap f from hs.symm ▸ AddSubgroup.mem_top b)

/-- The complement of a proper linear subspace generates the additive space. -/
theorem eq_top_of_outside_subspace {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W] (S : AddSubgroup W)
    (L : Submodule K W) (x : W) (hx : x ∉ L)
    (hout : ∀ w, w ∉ L → w ∈ S) : S = ⊤ := by
  apply top_unique
  intro w _
  by_cases hw : w ∈ L
  · have hwx : w + x ∉ L := by
      intro h
      exact hx ((L.add_mem_iff_right hw).mp h)
    have h := S.sub_mem (hout (w+x) hwx) (hout x hx)
    simpa only [add_sub_cancel_right] using h
  · exact hout w hw

end CubeGeneration
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
