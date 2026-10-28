module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Theory.AlgebraicGroup.Tori.Character.Regular

universe u

/-! Classification of characters of a standard diagonal torus. -/

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma dLaurentPointCharacters_linearIndependent (n : ℕ) :
    LinearIndependent k
      (fun z : Fin n → ℤ =>
        (dLaurentPointCharacter (k := k) n z :
          Variety.Point (dVariety k n) → k)) :=
  (linearIndependent_monoidHom
      (Variety.Point (dVariety k n)) k).comp
    (dLaurentPointCharacter (k := k) n)
    (dLaurentPointCharacter_injective (k := k) n)

private lemma dLaurentPointCharacter_mem_span_right_translates
    (n : ℕ) (p : MvPolynomial (dVariety k n).Coordinates k)
    {z : Fin n → ℤ} (hz : z ∈ (dLaurentCoefficients n p).support) :
    (dLaurentPointCharacter n z :
        Variety.Point (dVariety k n) → k) ∈
      Submodule.span k (Set.range fun t : Variety.Point (dVariety k n) =>
        fun x => evalPolynomial (x * t).val p) := by
  let c : (Fin n → ℤ) →₀ k := dLaurentCoefficients n p
  let S := c.support
  let chars : S → (Variety.Point (dVariety k n) → k) :=
    fun w => dLaurentPointCharacter n w.1
  have hchars : LinearIndependent k chars := by
    exact (dLaurentPointCharacters_linearIndependent (k := k) n).comp
      (fun w : S => w.1) Subtype.coe_injective
  let v : Variety.Point (dVariety k n) → S → k :=
    fun t w => c w.1 * chars w t
  let W : Submodule k (S → k) := Submodule.span k (Set.range v)
  have hW : W = ⊤ := by
    rw [← Submodule.dualAnnihilator_eq_bot_iff]
    apply le_antisymm
    · intro φ hφ
      rw [Submodule.mem_bot]
      apply LinearMap.ext
      intro a
      have hcoord (w : S) : φ (Pi.single w (1 : k)) = 0 := by
        have hsumfun :
            ∑ w : S, (φ (Pi.single w (1 : k)) * c w.1) • chars w = 0 := by
          funext t
          have hvt : v t ∈ W :=
            Submodule.subset_span (Set.mem_range_self t)
          have hzero := (Submodule.mem_dualAnnihilator φ).mp hφ (v t) hvt
          have hvsum :
              v t = ∑ w : S,
                (c w.1 * chars w t) • Pi.single w (1 : k) := by
            funext q
            simp [v, Pi.single_apply]
          rw [hvsum, map_sum] at hzero
          simpa [map_smul, smul_eq_mul, mul_assoc, mul_left_comm,
            mul_comm] using hzero
        have hcoeff :=
          (linearIndependent_iff'.mp hchars) Finset.univ
            (fun w : S => φ (Pi.single w (1 : k)) * c w.1)
            hsumfun w (Finset.mem_univ w)
        have hcw : c w.1 ≠ 0 := Finsupp.mem_support_iff.mp w.2
        exact (mul_eq_zero.mp hcoeff).resolve_right hcw
      have hasum : a = ∑ w : S, a w • Pi.single w (1 : k) := by
        funext q
        simp [Pi.single_apply]
      rw [hasum, map_sum]
      simp [hcoord]
    · exact bot_le
  let wz : S := ⟨z, hz⟩
  have hone : Pi.single wz (1 : k) ∈ W := by
    rw [hW]
    trivial
  obtain ⟨a, ha⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp hone
  let L : (S → k) →ₗ[k] (Variety.Point (dVariety k n) → k) :=
    Fintype.linearCombination k chars
  have hLv (t : Variety.Point (dVariety k n)) :
      L (v t) = fun x => evalPolynomial (x * t).val p := by
    funext x
    rw [evalPolynomial_eq_dLaurentPointCharacters_sum]
    simp only [L, v, c, S, chars, Fintype.linearCombination_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ w : S, (c w.1 * chars w t) * chars w x) =
      c.sum fun w a => a * dLaurentPointCharacter n w (x * t)
    rw [Finsupp.sum]
    conv_rhs => rw [← Finset.sum_attach]
    rw [Finset.univ_eq_attach]
    apply Finset.sum_congr rfl
    intro w hw
    rw [map_mul]
    ring
  have hLsingle : L (Pi.single wz (1 : k)) =
      (dLaurentPointCharacter n z :
        Variety.Point (dVariety k n) → k) := by
    simp [L, chars, wz, Fintype.linearCombination_apply,
      Pi.single_apply]
  refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨a, ?_⟩
  have hLa := congrArg L ha
  rw [map_finsuppSum] at hLa
  simp_rw [map_smul, hLv] at hLa
  rw [hLsingle] at hLa
  exact hLa

/-- A Laurent character occurring in a coordinate polynomial of a morphism
from `D_n` is the pullback of a polynomial on the target. -/
public theorem exists_target_polynomial_eq_dLaurentPointCharacter_of_mem_support
    {H : Variety k} [AlgebraicGroup H]
    (n : ℕ) (f : Theory.AlgebraicGroup.Morphism (dVariety k n) H)
    (i : H.Coordinates)
    (p : MvPolynomial (dVariety k n).Coordinates k)
    (hp : ∀ x : Variety.Point (dVariety k n),
      (f.onPoints x).val i = evalPolynomial x.val p)
    {z : Fin n → ℤ} (hz : z ∈ (dLaurentCoefficients n p).support) :
    ∃ q : MvPolynomial H.Coordinates k,
      ∀ x : Variety.Point (dVariety k n),
        evalPolynomial (f.onPoints x).val q =
          dLaurentPointCharacter n z x := by
  have hspan := dLaurentPointCharacter_mem_span_right_translates
    (k := k) n p hz
  refine Submodule.span_induction
    (p := fun g _ => ∃ q : MvPolynomial H.Coordinates k,
      ∀ x : Variety.Point (dVariety k n),
        evalPolynomial (f.onPoints x).val q = g x) ?_ ?_ ?_ ?_ hspan
  · intro g hg
    rcases hg with ⟨t, rfl⟩
    rcases (rightMulMorphism H (f.onPoints t)).regular i with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    intro x
    calc
      evalPolynomial (f.onPoints x).val q =
          ((rightMulMorphism H (f.onPoints t)).toFun
            (f.onPoints x)).val i := (hq (f.onPoints x)).symm
      _ = (f.onPoints x * f.onPoints t).val i := by
        rw [rightMulMorphism_apply]
      _ = (f.onPoints (x * t)).val i :=
        congrArg (fun y => y.val i) (f.map_mul x t).symm
      _ = evalPolynomial (x * t).val p := hp (x * t)
  · exact ⟨0, by intro x; simp [evalPolynomial]⟩
  · intro g h _ _ hg hh
    rcases hg with ⟨q, hq⟩
    rcases hh with ⟨r, hr⟩
    refine ⟨q + r, ?_⟩
    intro x
    calc
      evalPolynomial (f.onPoints x).val (q + r) =
          evalPolynomial (f.onPoints x).val q +
            evalPolynomial (f.onPoints x).val r := by
        exact map_add (MvPolynomial.eval (f.onPoints x).val) q r
      _ = g x + h x := by rw [hq x, hr x]
      _ = (g + h) x := rfl
  · intro a g _ hg
    rcases hg with ⟨q, hq⟩
    refine ⟨MvPolynomial.C a * q, ?_⟩
    intro x
    calc
      evalPolynomial (f.onPoints x).val (MvPolynomial.C a * q) =
          a * evalPolynomial (f.onPoints x).val q := by
        rw [evalPolynomial_mul]
        simp [evalPolynomial]
      _ = a * g x := congrArg (fun b => a * b) (hq x)
      _ = (a • g) x := rfl

/-- Every algebraic character of `D_n` is represented by an integral Laurent
exponent vector. -/
public theorem dLaurentCharacter_surjective (n : ℕ) :
    Function.Surjective (dLaurentCharacter (k := k) n) := by
  intro χ
  obtain ⟨p, hp⟩ := χ.scalarPolynomialFunction.representedBy
  let c : (Fin n → ℤ) →₀ k := dLaurentCoefficients n p
  have hexp (x : Variety.Point (dVariety k n)) :
      χ.pointCharacter x = c.sum fun z a =>
        a * dLaurentPointCharacter n z x := by
    rw [← TorusCharacter.scalarPolynomialFunction_apply χ x, hp x,
      evalPolynomial_eq_dLaurentPointCharacters_sum]
  have hc : c ≠ 0 := by
    intro hc
    have h := hexp (1 : Variety.Point (dVariety k n))
    rw [hc] at h
    rw [map_one] at h
    exact one_ne_zero h
  obtain ⟨z, hz⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hexp' (q : Variety.Point (dVariety k n)) :
      χ.pointCharacter q =
        ∑ w ∈ c.support, c w * dLaurentPointCharacter n w q := by
    simpa [Finsupp.sum] using hexp q
  have hpoint : χ.pointCharacter = dLaurentPointCharacter n z := by
    ext y
    have hsum :
        ∑ w ∈ c.support,
          (c w * (dLaurentPointCharacter n w y - χ.pointCharacter y)) •
            (dLaurentPointCharacter n w :
              Variety.Point (dVariety k n) → k) = 0 := by
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      calc
        ∑ w ∈ c.support,
            (c w * (dLaurentPointCharacter n w y - χ.pointCharacter y)) *
              dLaurentPointCharacter n w x =
            ∑ w ∈ c.support,
              (c w * dLaurentPointCharacter n w (x * y) -
                χ.pointCharacter y *
                  (c w * dLaurentPointCharacter n w x)) := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [map_mul]
            ring
        _ = (∑ w ∈ c.support,
              c w * dLaurentPointCharacter n w (x * y)) -
            ∑ w ∈ c.support,
              χ.pointCharacter y *
                (c w * dLaurentPointCharacter n w x) := by
            rw [Finset.sum_sub_distrib]
        _ = (∑ w ∈ c.support,
              c w * dLaurentPointCharacter n w (x * y)) -
            χ.pointCharacter y *
              (∑ w ∈ c.support,
                c w * dLaurentPointCharacter n w x) := by
            rw [Finset.mul_sum]
        _ = χ.pointCharacter (x * y) -
            χ.pointCharacter y * χ.pointCharacter x := by
            rw [← hexp' (x * y), ← hexp' x]
        _ = 0 := by
            rw [map_mul]
            ring
    have hcoeff :=
      (linearIndependent_iff'.mp
        (dLaurentPointCharacters_linearIndependent (k := k) n))
        c.support
        (fun w => c w *
          (dLaurentPointCharacter n w y - χ.pointCharacter y))
        hsum z hz
    have hcz : c z ≠ 0 := Finsupp.mem_support_iff.mp hz
    have hzero : dLaurentPointCharacter n z y - χ.pointCharacter y = 0 :=
      (mul_eq_zero.mp hcoeff).resolve_left hcz
    exact (sub_eq_zero.mp hzero).symm
  refine ⟨z, ?_⟩
  exact TorusCharacter.pointCharacter_injective
    (hpoint.trans
      (TorusCharacter.pointCharacter_dLaurentCharacter n z).symm).symm

end Theory.AlgebraicGroup
