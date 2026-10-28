module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.Basic

/-!
# Correction-root support and height

A root that is a strictly positive integral combination of two supported
roots is again supported and has height greater than both. For a radical
support, choose a nonzero simple-root coefficient outside the Levi nodes;
positivity prevents its cancellation in the combination. This works for
both selected Levi subsystems and does not depend on the coefficient field.

This is the support calculation used in the Chevalley root collection
underlying Aschbacher–Smith F.1.12(I)(5), printed p.263 of
`refs/quasithin.pdf`.
-/

@[expose] public section

open Theory.AlgebraicGroup StandardRootSystem
open scoped BigOperators
namespace ReeF4.Parabolics.RadicalCoordinates
noncomputable section

/-- Roots in the strictly positive integral cone spanned by two roots. -/
def PositiveCone (r s t : F4Chevalley.Root) : Prop :=
  ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
    typeF4RootPairing.root t = p • typeF4RootPairing.root r + q • typeF4RootPairing.root s

/-- The first correction root in a Chevalley exchange. -/
theorem positiveCone_of_add {r s t : F4Chevalley.Root}
    (h : typeF4RootPairing.root t =
      typeF4RootPairing.root r + typeF4RootPairing.root s) : PositiveCone r s t :=
  ⟨1, 1, by decide, by decide, by simpa only [one_nsmul] using h⟩

/-- The second correction root when the first input is short. -/
theorem positiveCone_of_two_add {r s t : F4Chevalley.Root}
    (h : typeF4RootPairing.root t =
      (2 : ℕ) • typeF4RootPairing.root r + typeF4RootPairing.root s) : PositiveCone r s t :=
  ⟨2, 1, by decide, by decide, by simpa only [one_nsmul] using h⟩

/-- The second correction root when the second input is short. -/
theorem positiveCone_of_add_two {r s t : F4Chevalley.Root}
    (h : typeF4RootPairing.root t =
      typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root s) : PositiveCone r s t :=
  ⟨1, 2, by decide, by decide, by simpa only [one_nsmul] using h⟩

private lemma coefficient_add (x y : Vec 4) (i : Fin 4) :
    typeF4SimpleCoefficient (x + y) i =
      typeF4SimpleCoefficient x i + typeF4SimpleCoefficient y i := by
  fin_cases i <;> simp [typeF4SimpleCoefficient] <;> ring

private lemma coefficient_nsmul (n : ℕ) (x : Vec 4) (i : Fin 4) :
    typeF4SimpleCoefficient (n • x) i = n * typeF4SimpleCoefficient x i := by
  fin_cases i <;> simp [typeF4SimpleCoefficient] <;> ring

private lemma coefficient_simple (i j : Fin 4) :
    typeF4SimpleCoefficient (typeF4SimpleRoot i) j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [typeF4SimpleRoot, typeF4SimpleCoefficient, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

private lemma positive_coefficients {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) (i : Fin 4) :
    0 ≤ typeF4SimpleCoefficient r.val i := by
  apply hr.induction_on_add
  · intro r hr
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨r, hr⟩
    have h : typeF4SimpleRoot j = r.val := congrArg (fun x => x.val.val) hj
    rw [← h, coefficient_simple]
    split <;> norm_num
  · intro r s t h hr hs
    change t.val = r.val + s.val at h
    rw [h, coefficient_add]
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨s, hs⟩
    have h : typeF4SimpleRoot j = s.val := congrArg (fun x => x.val.val) hj
    rw [← h, coefficient_simple]
    split <;> linarith

private lemma height_combination {r s t : F4Chevalley.Root} {p q : ℕ}
    (h : typeF4RootPairing.root t =
      p • typeF4RootPairing.root r + q • typeF4RootPairing.root s) :
    typeF4RootPairing_base.height t =
      p * typeF4RootPairing_base.height r + q * typeF4RootPairing_base.height s := by
  classical
  obtain ⟨f, _, _, hf⟩ := typeF4RootPairing_base.exists_root_eq_sum_int r
  obtain ⟨g, _, _, hg⟩ := typeF4RootPairing_base.exists_root_eq_sum_int s
  have ht : typeF4RootPairing.root t = ∑ j ∈ typeF4RootPairing_base.support,
      ((p : ℤ) * f j + (q : ℤ) * g j) • typeF4RootPairing.root j := by
    rw [h, hf, hg]
    simp only [Finset.smul_sum, add_smul, mul_smul, ← Finset.sum_add_distrib,
      Nat.cast_smul_eq_nsmul]
  rw [typeF4RootPairing_base.height_eq_sum ht,
    typeF4RootPairing_base.height_eq_sum hf,
    typeF4RootPairing_base.height_eq_sum hg]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- Every positive integral combination that is a root stays in the chosen
positive or radical support and has greater height than either input. -/
theorem positiveCone_supported_degree {k : Support} (r s : Root k)
    {t : F4Chevalley.Root} (ht : PositiveCone r.val s.val t) :
    Supported k t ∧ max (rootDegree r.val) (rootDegree s.val) < rootDegree t := by
  obtain ⟨p, q, hp, hq, he⟩ := ht
  have hr := supported_isPos r
  have hs := supported_isPos s
  have hh := height_combination he
  have hpr : typeF4RootPairing_base.height r.val ≤
      (p : ℤ) * typeF4RootPairing_base.height r.val :=
    le_mul_of_one_le_left (le_of_lt hr) (by exact_mod_cast hp)
  have hqs : typeF4RootPairing_base.height s.val ≤
      (q : ℤ) * typeF4RootPairing_base.height s.val :=
    le_mul_of_one_le_left (le_of_lt hs) (by exact_mod_cast hq)
  have htpos : typeF4RootPairing_base.IsPos t := by
    change 0 < typeF4RootPairing_base.height t
    change 0 < typeF4RootPairing_base.height r.val at hr
    change 0 < typeF4RootPairing_base.height s.val at hs
    omega
  constructor
  · cases k with
    | positive => exact htpos
    | radical side =>
      obtain ⟨i, hi, hri⟩ := r.property.2
      refine ⟨htpos, i, hi, ?_⟩
      change t.val = p • r.val.val + q • s.val.val at he
      rw [he, coefficient_add, coefficient_nsmul, coefficient_nsmul]
      exact ne_of_gt (add_pos_of_pos_of_nonneg
        (mul_pos (by exact_mod_cast hp)
          (lt_of_le_of_ne (positive_coefficients hr i) (Ne.symm hri)))
        (mul_nonneg (Nat.cast_nonneg q) (positive_coefficients hs i)))
  · have hrt := rootDegree_cast r
    have hst := rootDegree_cast s
    have htt : (rootDegree t : ℤ) = typeF4RootPairing_base.height t :=
      Int.toNat_of_nonneg (le_of_lt htpos)
    change 0 < typeF4RootPairing_base.height r.val at hr
    change 0 < typeF4RootPairing_base.height s.val at hs
    omega

end
end ReeF4.Parabolics.RadicalCoordinates
