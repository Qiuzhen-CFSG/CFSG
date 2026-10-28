module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding.SplittingSeed

/-!
# An explicit split basis for the quadratic octonion algebra

Choose d nonzero with σ(d) = -d and t with t σ(t) = -1. In coordinates
`(a,u₀,u₁,u₂)`, the two diagonal idempotents are `(1/2,±t/2,0,0)`.
The three upper Peirce vectors are
`(-1/(2d),t/(2d),0,0)`, `(0,0,1/2,-1/(2t))`, `(0,0,d/2,d/(2t))`;
the corresponding lower vectors are
`(d/2,dt/2,0,0)`, `(0,0,1/2,1/(2t))`, `(0,0,-1/(2d),1/(2dt))`.

`splitMap` combines these vectors in the literal Wilson-table order.
The coordinate calculation proves preservation of that multiplication.
Conjugating a linear relation separates its real and imaginary coefficients,
proving injectivity; both F-spaces have dimension eight, hence the map is
an equivalence. Norm surjectivity and the genuine quadratic Frobenius supply
all chosen scalars. No algebra classification or model comparison is assumed.

This supplies the split-algebra input to the faithful SU₃ embedding needed
for Aschbacher–Smith I.1.2–I.1.4 and GLS III §6.1. The multiplication table
is the licensed ATLAS port, LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Matrix Atlas.SplitOctonion
namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding
noncomputable section
variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

@[simp] theorem conj_algebraMap (a : F) :
    quadraticConj F p (algebraMap F (Quadratic F p) a) = algebraMap F (Quadratic F p) a :=
  (FiniteField.Extension.frob F p 2).commutes a

def splitMap (d t : Quadratic F p) (x : Carrier F) : Octonion F p :=
  let z := fun i => algebraMap F (Quadratic F p) (x i)
  ((z 3 + z 4 - z 0 / d + z 7 * d) / 2,
    ![t * (z 3 - z 4 + z 0 / d + z 7 * d) / 2,
      (z 5 + z 2 + z 6 * d - z 1 / d) / 2,
      (-z 5 + z 2 + z 6 * d + z 1 / d) / (2 * t)])

def splitLinear (d t : Quadratic F p) : Carrier F →ₗ[F] Octonion F p where
  toFun := splitMap F p d t
  map_add' x y := by
    apply Prod.ext
    · simp [splitMap]
      ring
    · funext i
      fin_cases i <;> simp [splitMap] <;> ring
  map_smul' r x := by
    apply Prod.ext
    · simp [splitMap, Algebra.smul_def]
      ring
    · funext i
      fin_cases i <;> simp [splitMap, Algebra.smul_def] <;> ring

theorem splitLinear_mul (h2 : (2 : Quadratic F p) ≠ 0) (d t : Quadratic F p)
    (hd : d ≠ 0) (hsd : quadraticConj F p d = -d)
    (ht : t * quadraticConj F p t = -1) (x y : Carrier F) :
    splitLinear F p d t (mul x y) =
      octonionMul F p (splitLinear F p d t x) (splitLinear F p d t y) := by
  have ht0 : t ≠ 0 := by intro h; simp [h] at ht
  have hst : quadraticConj F p t = -t⁻¹ := by
    calc
      _ = t⁻¹ * (t * quadraticConj F p t) := by rw [← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
      _ = _ := by rw [ht]; ring
  apply Prod.ext
  · simp [splitLinear, splitMap, octonionMul, mul, dotProduct, Fin.sum_univ_three,
      hsd, hst, map_ofNat]
    field_simp [h2, hd, ht0]
    ring
  · funext i
    fin_cases i <;>
      simp [splitLinear, splitMap, octonionMul, mul, cross_apply, Matrix.vecHead,
        Matrix.vecTail, hsd, hst, map_ofNat] <;>
      field_simp [h2, hd, ht0] <;> ring

/-- Real and nonzero trace-zero coordinates are independent over F. -/
theorem base_imaginary_independent (h2 : (2 : Quadratic F p) ≠ 0)
    (d : Quadratic F p) (hd : d ≠ 0) (hsd : quadraticConj F p d = -d)
    (a b : F) (h : algebraMap F (Quadratic F p) a +
      algebraMap F (Quadratic F p) b * d = 0) : a = 0 ∧ b = 0 := by
  have hc := congrArg (quadraticConj F p) h
  simp only [map_add, map_mul, conj_algebraMap, hsd, map_zero] at hc
  have hbd : (2 : Quadratic F p) * (algebraMap F (Quadratic F p) b * d) = 0 := by
    linear_combination h - hc
  have hb := (mul_eq_zero.mp ((mul_eq_zero.mp hbd).resolve_left h2)).resolve_right hd
  have ha : algebraMap F (Quadratic F p) a = 0 := by
    simpa only [hb, zero_mul, add_zero] using h
  exact ⟨(algebraMap F (Quadratic F p)).injective (ha.trans (map_zero _).symm),
    (algebraMap F (Quadratic F p)).injective (hb.trans (map_zero _).symm)⟩

theorem splitLinear_injective (h2 : (2 : Quadratic F p) ≠ 0)
    (d t : Quadratic F p) (hd : d ≠ 0) (hsd : quadraticConj F p d = -d)
    (ht : t ≠ 0) : Function.Injective (splitLinear F p d t) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  let z := fun i => algebraMap F (Quadratic F p) (x i)
  have ha := congrArg Prod.fst hx
  have hb := congrArg (fun w : Octonion F p => w.2 0) hx
  have hc := congrArg (fun w : Octonion F p => w.2 1) hx
  have he := congrArg (fun w : Octonion F p => w.2 2) hx
  change (z 3 + z 4 - z 0 / d + z 7 * d) / 2 = 0 at ha
  change t * (z 3 - z 4 + z 0 / d + z 7 * d) / 2 = 0 at hb
  change (z 5 + z 2 + z 6 * d - z 1 / d) / 2 = 0 at hc
  change (-z 5 + z 2 + z 6 * d + z 1 / d) / (2 * t) = 0 at he
  have ha := (div_eq_zero_iff.mp ha).resolve_right h2
  have hb := (mul_eq_zero.mp ((div_eq_zero_iff.mp hb).resolve_right h2)).resolve_left ht
  have hc := (div_eq_zero_iff.mp hc).resolve_right h2
  have he := (div_eq_zero_iff.mp he).resolve_right (mul_ne_zero h2 ht)
  have hz37 : z 3 + z 7 * d = 0 := by
    apply (mul_eq_zero.mp (show (2 : Quadratic F p) * (z 3 + z 7 * d) = 0 from ?_)).resolve_left h2
    linear_combination ha + hb
  have hz40 : z 4 - z 0 / d = 0 := by
    apply (mul_eq_zero.mp (show (2 : Quadratic F p) * (z 4 - z 0 / d) = 0 from ?_)).resolve_left h2
    linear_combination ha - hb
  have hz04 : -z 0 + z 4 * d = 0 := by
    calc
      _ = (z 4 - z 0 / d) * d := by field_simp [hd]; ring
      _ = 0 := by rw [hz40, zero_mul]
  have hz26 : z 2 + z 6 * d = 0 := by
    apply (mul_eq_zero.mp (show (2 : Quadratic F p) * (z 2 + z 6 * d) = 0 from ?_)).resolve_left h2
    linear_combination hc + he
  have hz51 : z 5 - z 1 / d = 0 := by
    apply (mul_eq_zero.mp (show (2 : Quadratic F p) * (z 5 - z 1 / d) = 0 from ?_)).resolve_left h2
    linear_combination hc - he
  have hz15 : -z 1 + z 5 * d = 0 := by
    calc
      _ = (z 5 - z 1 / d) * d := by field_simp [hd]; ring
      _ = 0 := by rw [hz51, zero_mul]
  obtain ⟨h3, h7⟩ := base_imaginary_independent F p h2 d hd hsd (x 3) (x 7) hz37
  obtain ⟨h0, h4⟩ := base_imaginary_independent F p h2 d hd hsd (-x 0) (x 4)
    (by simpa only [map_neg] using hz04)
  obtain ⟨h2x, h6⟩ := base_imaginary_independent F p h2 d hd hsd (x 2) (x 6) hz26
  obtain ⟨h1, h5⟩ := base_imaginary_independent F p h2 d hd hsd (-x 1) (x 5)
    (by simpa only [map_neg] using hz15)
  have h0 := neg_eq_zero.mp h0
  have h1 := neg_eq_zero.mp h1
  ext i
  fin_cases i <;> assumption

/-- The actual comparison of the two eight-dimensional F-vector spaces. -/
def splitEquiv (h2 : (2 : Quadratic F p) ≠ 0)
    (d t : Quadratic F p) (hd : d ≠ 0) (hsd : quadraticConj F p d = -d)
    (ht : t ≠ 0) : Carrier F ≃ₗ[F] Octonion F p :=
  (splitLinear F p d t).linearEquivOfInjective
    (splitLinear_injective F p h2 d t hd hsd ht)
    (by rw [finrank_octonion]; simp [Carrier])

theorem exists_split_comparison (hp : 3 < p) :
    ∃ e : Octonion F p ≃ₗ[F] Carrier F,
      ∀ x y, e (octonionMul F p x y) = mul (e x) (e y) := by
  have h2 : (2 : Quadratic F p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (Quadratic F p) Nat.prime_two (by omega : p ≠ 2)
  obtain ⟨d, hd, hsd⟩ := exists_trace_zero_generator F p
  obtain ⟨t, ht⟩ := exists_norm_minus_one F p
  have ht0 : t ≠ 0 := by intro h; simp [h] at ht
  let e := splitEquiv F p h2 d t hd hsd ht0
  refine ⟨e.symm, ?_⟩
  intro x y
  apply e.injective
  rw [e.apply_symm_apply]
  change octonionMul F p x y = splitLinear F p d t (mul (e.symm x) (e.symm y))
  rw [splitLinear_mul F p h2 d t hd hsd ht]
  exact congrArg₂ (octonionMul F p) (e.apply_symm_apply x).symm (e.apply_symm_apply y).symm

/-- A proved comparison with the literal split-octonion multiplication table. -/
def splitComparison (hp : 3 < p) : Octonion F p ≃ₗ[F] Carrier F :=
  Classical.choose (exists_split_comparison F p hp)

theorem splitComparison_mul (hp : 3 < p) (x y : Octonion F p) :
    splitComparison F p hp (octonionMul F p x y) =
      mul (splitComparison F p hp x) (splitComparison F p hp y) :=
  Classical.choose_spec (exists_split_comparison F p hp) x y

end
end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding
