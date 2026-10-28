module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.WeylGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations.SignedBrackets
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations.Exponential

/-!
# Multiplication of the main curves in the relative B₂ blocks

The integral B₂ brackets and finite-exponential calculation give the exact
split swap with corrections ab and ab². The four zero brackets give the
mixed-length commutations. In characteristic two every split root element
is an involution; the swap's involutive correction then commutes with the
short factor. Cancelling its commuting highest-root factor proves the
remaining short-root commutation.

Collecting two main words now gives the type-V product formula with central
parameter t^(2θ)u. The field identity θ(2θ(t)) = t accounts for its mixed-root
coordinate. The proof holds for every even block index and every m, including
zero, and thus supplies the third-block multiplication in `RootRelations`.

Source: GLS3 Table 2.4, type V, `refs/KGroup/GLS3/chapter2.tex`.
The application is Aschbacher–Smith F.1.12(II)(i), printed pp.263–264.
-/

public section

open Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open RadicalCoordinates.FixedCoordinates
open RadicalCoordinates.FixedCoordinates.MatrixRelations
namespace MatrixRelations
noncomputable section

private theorem root_add (m : ℕ) (r : F4Chevalley.Root) (a b : CoefficientField m) :
    rootGeneratorInGroup m r (a + b) = rootGeneratorInGroup m r a * rootGeneratorInGroup m r b :=
  Subtype.ext (F4Chevalley.rootCurve_add r a b)

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem root_mul_self (m : ℕ) (r : F4Chevalley.Root) (a : CoefficientField m) :
    rootGeneratorInGroup m r a * rootGeneratorInGroup m r a = 1 := by
  rw [← root_add, CharTwo.add_self_eq_zero, root_zero]

-- The involutive correction to two involutions commutes with both inputs.
private theorem correction_commute {G : Type*} [Group G] (A B C : G)
    (hA : A * A = 1) (hB : B * B = 1) (hC : C * C = 1)
    (h : B * A = A * B * C) : Commute B C := by
  have hAi : A⁻¹ = A := inv_eq_of_mul_eq_one_left hA
  have hBi : B⁻¹ = B := inv_eq_of_mul_eq_one_left hB
  have hCi : C⁻¹ = C := inv_eq_of_mul_eq_one_left hC
  have hi := congrArg Inv.inv h
  simp only [mul_inv_rev, hAi, hBi, hCi] at hi
  have h₁ := congrArg (fun x => A * x) h
  have h₂ := congrArg (fun x => x * A) hi
  simp only [← mul_assoc, hA, one_mul] at h₁
  simp only [mul_assoc, hA, mul_one] at h₂
  exact h₁.symm.trans (by simpa only [mul_assoc] using h₂)

private theorem root_commute (m : ℕ) (r s : F4Chevalley.Root)
    (h : Commute (F4Chevalley.integralOperators.rootOperator r)
      (F4Chevalley.integralOperators.rootOperator s)) (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m r a) (rootGeneratorInGroup m s b) :=
  Subtype.ext (rootCurves_commute_of_operators_commute r s h a b).eq

private theorem short_mixed_commute (m : ℕ) (r s c d : F4Chevalley.Root)
    (h : IntegralB2Relations r s c d) (b z : CoefficientField m) :
    Commute (rootGeneratorInGroup m s b) (rootGeneratorInGroup m c z) := by
  by_cases hb : b = 0
  · subst b
    rw [root_zero]
    exact Commute.one_left _
  have hw := rootCurve_swap_of_integralB2 m r s c d h (z / b) b
  have hw' : rootGeneratorInGroup m s b * rootGeneratorInGroup m r (z / b) =
      rootGeneratorInGroup m r (z / b) * rootGeneratorInGroup m s b *
        rootGeneratorInGroup m c z * rootGeneratorInGroup m d ((z / b) * b ^ 2) := by
    apply Subtype.ext
    change F4Chevalley.rootCurve s b * F4Chevalley.rootCurve r (z / b) =
      F4Chevalley.rootCurve r (z / b) * F4Chevalley.rootCurve s b *
        F4Chevalley.rootCurve c z * F4Chevalley.rootCurve d ((z / b) * b ^ 2)
    simpa only [div_mul_cancel₀ _ hb] using hw
  have hCD := root_commute m c d h.sum_top z ((z / b) * b ^ 2)
  have hE :
      (rootGeneratorInGroup m c z * rootGeneratorInGroup m d ((z / b) * b ^ 2)) *
      (rootGeneratorInGroup m c z * rootGeneratorInGroup m d ((z / b) * b ^ 2)) = 1 := by
    rw [hCD.symm.mul_mul_mul_comm, root_mul_self, root_mul_self, one_mul]
  have he := correction_commute _ _ _ (root_mul_self m _ _) (root_mul_self m _ _) hE
    (by simpa only [mul_assoc] using hw')
  have hBD := root_commute m s d h.short_top b ((z / b) * b ^ 2)
  simpa only [mul_assoc, root_mul_self, mul_one] using he.mul_right hBD

private theorem b2_main_product (m : ℕ) (r s c d : F4Chevalley.Root)
    (h : IntegralB2Relations r s c d) (t u : CoefficientField m) :
    (rootGeneratorInGroup m r t * rootGeneratorInGroup m s (halfFrobenius m t) *
      rootGeneratorInGroup m c (t * halfFrobenius m t)) *
    (rootGeneratorInGroup m r u * rootGeneratorInGroup m s (halfFrobenius m u) *
      rootGeneratorInGroup m c (u * halfFrobenius m u)) =
    (rootGeneratorInGroup m r (t + u) * rootGeneratorInGroup m s (halfFrobenius m (t + u)) *
      rootGeneratorInGroup m c ((t + u) * halfFrobenius m (t + u))) *
    (rootGeneratorInGroup m d (titsEnd m t * u) *
      rootGeneratorInGroup m c (halfFrobenius m (titsEnd m t * u))) := by
  let A := rootGeneratorInGroup m r
  let B := rootGeneratorInGroup m s
  let C := rootGeneratorInGroup m c
  let D := rootGeneratorInGroup m d
  let f := halfFrobenius m
  let q := titsEnd m t * u
  have hA (a b) : A (a + b) = A a * A b := root_add m _ a b
  have hB (a b) : B (a + b) = B a * B b := root_add m _ a b
  have hC (a b) : C (a + b) = C a * C b := root_add m _ a b
  have hAC (a b) : Commute (A a) (C b) := root_commute m r c h.long_sum a b
  have hBC (a b) : Commute (B a) (C b) := short_mixed_commute m r s c d h a b
  have hDB (a b) : Commute (D a) (B b) := (root_commute m s d h.short_top b a).symm
  have hDC (a b) : Commute (D a) (C b) := (root_commute m c d h.sum_top b a).symm
  have hw : B (f t) * A u = A u * B (f t) * C (u * f t) * D q := by
    apply Subtype.ext
    change F4Chevalley.rootCurve s (f t) * F4Chevalley.rootCurve r u =
      F4Chevalley.rootCurve r u * F4Chevalley.rootCurve s (f t) *
        F4Chevalley.rootCurve c (u * f t) * F4Chevalley.rootCurve d q
    simpa only [f, q, halfFrobenius_sq, mul_comm u] using
      rootCurve_swap_of_integralB2 m r s c d h u (f t)
  have hrest : Commute (C (u * f t) * D q * C (t * f t)) (B (f u)) :=
    (((hBC (f u) _).symm.mul_left (hDB q (f u))).mul_left (hBC (f u) _).symm)
  have hscalar : (t + u) * (f t + f u) + t * f u = u * f t + t * f t + u * f u := by
    calc
      _ = u * f t + t * f t + u * f u + (t * f u + t * f u) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
  change (A t * B (f t) * C (t * f t)) * (A u * B (f u) * C (u * f u)) =
    (A (t + u) * B (f (t + u)) * C ((t + u) * f (t + u))) * (D q * C (f q))
  have hfq : f q = t * f u := by simp only [f, q, map_mul, halfFrobenius_titsEnd]
  rw [map_add, hfq]
  calc
    _ = A t * B (f t) * (C (t * f t) * A u) * B (f u) * C (u * f u) := by
      simp only [mul_assoc]
    _ = A t * (B (f t) * A u) * C (t * f t) * B (f u) * C (u * f u) := by
      rw [(hAC u _).symm.eq]
      simp only [mul_assoc]
    _ = (A t * A u) * (B (f t) * (C (u * f t) * D q * C (t * f t)) * B (f u)) *
        C (u * f u) := by
      rw [hw]
      simp only [mul_assoc]
    _ = A (t + u) * (B (f t + f u) * (C (u * f t) * D q * C (t * f t))) *
        C (u * f u) := by
      rw [hrest.right_comm, ← hA, ← hB]
    _ = A (t + u) * B (f t + f u) * D q * C (u * f t + t * f t + u * f u) := by
      rw [(hDC q _).symm.eq, hC (u * f t + t * f t) (u * f u), hC]
      simp only [mul_assoc]
    _ = _ := by
      rw [← hscalar, hC]
      exact (hDC q ((t + u) * (f t + f u))).mul_mul_mul_comm _ _

/-- Every even relative block satisfies the full type-V main-parameter law. -/
theorem rootWord_even_mul (m : ℕ) (i : Fin 8) (hi : i.val % 2 = 0)
    (t u : CoefficientField m) :
    rootWord m i t * rootWord m i u =
      rootWord m i (t + u) * centralWord m i (titsEnd m t * u) := by
  have hd : dot (longRoot i).val (shortRoot i).val = -1 := by
    simp only [rootPair_dot, hi, ite_true]
  have hb := b2BracketRelations (longRoot i) (shortRoot i) (mixedRoot i) (highRoot i)
    (longRoot_pos i) (shortRoot_pos i) (longRoot_isLong i) (shortRoot_isShort i)
    hd (mixedRoot_eq_add i hi) (highRoot_eq_add_two i hi)
  have h := integralB2Relations_of_brackets (longRoot i) (shortRoot i) (mixedRoot i) (highRoot i)
    (longRoot_pos i) (shortRoot_pos i) (longRoot_isLong i) (shortRoot_isShort i)
    hd (mixedRoot_eq_add i hi) (highRoot_eq_add_two i hi) hb
  have hf : rootFieldEnd m (longRoot i) = halfFrobenius m := by
    simp only [rootFieldEnd, if_pos (longRoot_isLong i), halfFrobenius]
  simp only [rootWord, centralWord, hi, ite_true, hf]
  exact b2_main_product m (longRoot i) (shortRoot i) (mixedRoot i) (highRoot i) h t u

end
end MatrixRelations
end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
