module

public import Theory.AlgebraicGroup.Tori.Character.Laurent
public import Theory.AlgebraicGroup.Tori.Monomial

universe u

/-! Scalar Laurent characters on the point group of a diagonal torus. -/

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The scalar-valued monoid character on `D_n(k)` associated to an integral
Laurent exponent vector. -/
@[expose]
public def dLaurentPointCharacter (n : ℕ) (z : Fin n → ℤ) :
    Variety.Point (dVariety k n) →* k where
  toFun := fun x => ((↑(∏ i, (dPointEquiv n x i) ^ z i) : k))
  map_one' := by
    rw [dPointEquiv_one]
    simp
  map_mul' := by
    intro x y
    rw [dPointEquiv_mul]
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
    push_cast
    rfl

/-- Distinct integral exponent vectors define distinct scalar monoid
characters on `D_n(k)`. -/
public theorem dLaurentPointCharacter_injective [IsAlgClosed k] (n : ℕ) :
    Function.Injective (dLaurentPointCharacter (k := k) n) := by
  intro z w hzw
  funext j
  by_contra hj
  have hd : z j - w j ≠ 0 := sub_ne_zero.mpr hj
  obtain ⟨a, ha⟩ := exists_unit_zpow_ne_one (k := k) hd
  let x : Variety.Point (dVariety k n) :=
    (dPointEquiv n).symm (Pi.mulSingle j a)
  have hv := congrArg
    (fun χ : Variety.Point (dVariety k n) →* k => χ x) hzw
  have hx : dPointEquiv n x = Pi.mulSingle j a :=
    (dPointEquiv n).apply_symm_apply _
  have hz : (∏ i, (((Pi.mulSingle j a : Fin n → kˣ) i : k)) ^ z i) =
      (a : k) ^ z j := by
    calc
      _ = (((Pi.mulSingle j a : Fin n → kˣ) j : k)) ^ z j := by
        apply Fintype.prod_eq_single j
        intro i hij
        simp [hij]
      _ = _ := by simp
  have hw : (∏ i, (((Pi.mulSingle j a : Fin n → kˣ) i : k)) ^ w i) =
      (a : k) ^ w j := by
    calc
      _ = (((Pi.mulSingle j a : Fin n → kˣ) j : k)) ^ w j := by
        apply Fintype.prod_eq_single j
        intro i hij
        simp [hij]
      _ = _ := by simp
  have hv' : (a : k) ^ z j = (a : k) ^ w j := by
    simpa [dLaurentPointCharacter, hx, hz, hw] using hv
  apply ha
  rw [zpow_sub, mul_inv_eq_one]
  ext
  simpa only [Units.val_zpow_eq_zpow_val] using hv'

/-- The scalar-valued monoid character induced on rational points by an
algebraic character. -/
@[expose]
public noncomputable def TorusCharacter.pointCharacter
    {T : Variety k} [AlgebraicGroup T] (χ : TorusCharacter T) :
    Variety.Point T →* k where
  toFun := fun x => (dPointEquiv 1 (χ.onPoints x) 0 : k)
  map_one' := by
    have h := congrArg
      (fun q : Variety.Point (KMult k) => (dPointEquiv 1 q 0 : k))
      χ.onPoints.map_one
    rw [dPointEquiv_one] at h
    exact h
  map_mul' := by
    intro x y
    have h := congrArg
      (fun q : Variety.Point (KMult k) => (dPointEquiv 1 q 0 : k))
      (χ.onPoints.map_mul x y)
    rw [dPointEquiv_mul] at h
    exact h

/-- The scalar point character of a Laurent character is the explicit Laurent
point character with the same exponent. -/
public lemma TorusCharacter.pointCharacter_dLaurentCharacter
    (n : ℕ) (z : Fin n → ℤ) :
    TorusCharacter.pointCharacter (dLaurentCharacter (k := k) n z) =
      dLaurentPointCharacter n z := by
  ext x
  change (dPointEquiv 1
      ((dLaurentCharacter (k := k) n z).onPoints x) 0 : k) =
    ((↑(∏ i, (dPointEquiv n x i) ^ z i) : k))
  exact congrArg (fun a : kˣ => (a : k))
    (dLaurentCharacter_apply n z x)

/-- Algebraic characters are determined by their scalar-valued point
characters. -/
public theorem TorusCharacter.pointCharacter_injective
    {T : Variety k} [AlgebraicGroup T] :
    Function.Injective (TorusCharacter.pointCharacter (T := T)) := by
  intro χ ψ h
  apply Theory.AlgebraicGroup.Morphism.ext
  funext x
  apply (dPointEquiv 1).injective
  funext i
  fin_cases i
  apply Units.ext
  have hx := congrArg (fun f : Variety.Point T →* k => f x) h
  change (dPointEquiv 1 (χ.toVariety.toFun x) 0 : k) =
    (dPointEquiv 1 (ψ.toVariety.toFun x) 0 : k) at hx
  exact hx

/-- Evaluation of diagonal characters at a point, as a monoid homomorphism
into the group of `kˣ`-valued algebraic characters. -/
@[expose]
public noncomputable def dVarietyPointEval (n : ℕ) :
    Variety.Point (dVariety k n) →*
      (TorusCharacter (dVariety k n) →* kˣ) where
  toFun := fun x =>
    { toFun := fun f => dPointEquiv 1 (f.onPoints x) 0
      map_one' := by
        change dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 = 1
        rw [dPointEquiv_one]
        rfl
      map_mul' := by
        intro f g
        change dPointEquiv 1 (f.onPoints x * g.onPoints x) 0 =
          dPointEquiv 1 (f.onPoints x) 0 *
            dPointEquiv 1 (g.onPoints x) 0
        exact congrFun
          (dPointEquiv_mul 1 (f.onPoints x) (g.onPoints x)) 0 }
  map_one' := by
    ext f
    simp [dPointEquiv_one]
  map_mul' := by
    intro x y
    ext f
    simp [dPointEquiv_mul]

private lemma evalPolynomial_eq_dLaurentCoefficients_sum
    (n : ℕ)
    (p : MvPolynomial (dVariety k n).Coordinates k)
    (x : Variety.Point (dVariety k n)) :
    evalPolynomial x.val p =
      (dLaurentCoefficients n p).sum fun z a =>
        a * (dPointEquiv 1 ((dLaurentCharacter n z).onPoints x) 0 : k) := by
  change (AddMonoidAlgebra.coeff p).sum
    (fun s a => a * s.prod fun c e => x.val c ^ e) = _
  rw [dLaurentCoefficients, Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro s hs
    rw [dMonomial_value_eq_laurent, dLaurentCharacter_apply]
  · intro z
    simp
  · intro z a b
    ring

/-- The Laurent expansion of a coordinate polynomial, expressed using scalar
monoid characters on `D_n(k)`. -/
public theorem evalPolynomial_eq_dLaurentPointCharacters_sum
    (n : ℕ)
    (p : MvPolynomial (dVariety k n).Coordinates k)
    (x : Variety.Point (dVariety k n)) :
    evalPolynomial x.val p =
      (dLaurentCoefficients n p).sum fun z a =>
        a * dLaurentPointCharacter n z x := by
  rw [evalPolynomial_eq_dLaurentCoefficients_sum]
  apply Finsupp.sum_congr
  intro z hz
  rw [dLaurentCharacter_apply]
  rfl

end Theory.AlgebraicGroup
