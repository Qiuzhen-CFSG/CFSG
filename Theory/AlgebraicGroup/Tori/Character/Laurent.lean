module

public import Theory.AlgebraicGroup.Tori.Character.Basic

universe u

/-! Integral Laurent characters of standard diagonal tori. -/

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The character of `D_n` given by its `i`th diagonal coordinate. -/
@[expose]
public def dCoordinateCharacter (n : ℕ) (i : Fin n) :
    TorusCharacter (dVariety k n) := by
  let F : Variety.Morphism (dVariety k n) (KMult k) :=
    { toFun := fun x =>
        ⟨fun c => match c with
          | Sum.inl _ => x.val (Sum.inl (ULift.up i))
          | Sum.inr _ => x.val (Sum.inr (ULift.up i)), by
            intro p hp
            rcases Set.mem_ofPred.mp hp with ⟨j, rfl⟩
            simpa [evalPolynomial, dPointEntry, dPointEntryInv] using
              sub_eq_zero.mpr (dPoint_entry_mul_inv n x i)⟩
      regular := by
        intro c
        cases c with
        | inl j =>
            exact ⟨MvPolynomial.X (Sum.inl (ULift.up i)), fun x => by
              simp [evalPolynomial]⟩
        | inr j =>
            exact ⟨MvPolynomial.X (Sum.inr (ULift.up i)), fun x => by
              simp [evalPolynomial]⟩ }
  have hF (x : Variety.Point (dVariety k n)) :
      dPointEquiv 1 (F.toFun x) 0 = dPointEquiv n x i := by
    ext
    rfl
  refine
    { toVariety := F
      map_one := ?_
      map_mul := ?_ }
  · apply (dPointEquiv 1).injective
    rw [dPointEquiv_one]
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rw [hF, dPointEquiv_one]
    rfl
  · intro x y
    apply (dPointEquiv 1).injective
    rw [dPointEquiv_mul]
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change dPointEquiv n (x * y) i =
      dPointEquiv 1 (F.toFun x) 0 * dPointEquiv 1 (F.toFun y) 0
    rw [hF, hF]
    exact congrFun (dPointEquiv_mul n x y) i

/-- Evaluating the `i`th coordinate character returns the `i`th diagonal
coordinate. -/
public lemma dCoordinateCharacter_apply (n : ℕ) (i : Fin n)
    (x : Variety.Point (dVariety k n)) :
    dPointEquiv 1 ((dCoordinateCharacter n i).onPoints x) 0 =
      dPointEquiv n x i := by
  rfl

/-- The character of `D_n` represented by the Laurent exponent vector `z`. -/
@[expose]
public noncomputable def dLaurentCharacter (n : ℕ) (z : Fin n → ℤ) :
    TorusCharacter (dVariety k n) :=
  ∏ i, (dCoordinateCharacter n i) ^ z i

/-- The additive exponent-lattice homomorphism into the additive form of the
character group of `D_n`. -/
@[expose]
public noncomputable def dLaurentCharacterHom (n : ℕ) :
    (Fin n → ℤ) →+ Additive (TorusCharacter (dVariety k n)) where
  toFun := fun z => Additive.ofMul (dLaurentCharacter n z)
  map_zero' := by
    change dLaurentCharacter n 0 = 1
    simp [dLaurentCharacter]
  map_add' := by
    intro z w
    change dLaurentCharacter n (z + w) =
      dLaurentCharacter n z * dLaurentCharacter n w
    simp only [dLaurentCharacter, Pi.add_apply]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact zpow_add _ _ _

/-- Evaluation of a Laurent character is the corresponding Laurent monomial
in the diagonal entries. -/
public lemma dLaurentCharacter_apply
    (n : ℕ) (z : Fin n → ℤ) (x : Variety.Point (dVariety k n)) :
    dPointEquiv 1 ((dLaurentCharacter n z).onPoints x) 0 =
      ∏ i, (dPointEquiv n x i) ^ z i := by
  classical
  let ev : TorusCharacter (dVariety k n) →* kˣ :=
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
  change ev (∏ i, (dCoordinateCharacter n i) ^ z i) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_zpow]
  congr 1

/-- The single-coordinate Laurent character is the corresponding diagonal
coordinate character. -/
public lemma dLaurentCharacter_single (n : ℕ) (i : Fin n) :
    dLaurentCharacter (k := k) n (Pi.single i 1) =
      dCoordinateCharacter n i := by
  simp [dLaurentCharacter, Pi.single_apply]

/-- A Laurent character is the product of its single-coordinate characters. -/
public lemma dLaurentCharacter_expand (n : ℕ) (z : Fin n → ℤ) :
    dLaurentCharacter (k := k) n z =
      ∏ i, (dLaurentCharacter (k := k) n (Pi.single i 1)) ^ z i := by
  rw [dLaurentCharacter]
  apply Finset.prod_congr rfl
  intro i hi
  rw [dLaurentCharacter_single]

/-- Distinct integral exponent vectors define distinct characters of `D_n`. -/
public theorem dLaurentCharacter_injective [IsAlgClosed k] (n : ℕ) :
    Function.Injective (dLaurentCharacter (k := k) n) := by
  intro z w hzw
  funext j
  by_contra hj
  have hd : z j - w j ≠ 0 := sub_ne_zero.mpr hj
  obtain ⟨a, ha⟩ := exists_unit_zpow_ne_one (k := k) hd
  let x : Variety.Point (dVariety k n) :=
    (dPointEquiv n).symm (Pi.mulSingle j a)
  have hv := congrArg
    (fun χ : TorusCharacter (dVariety k n) =>
      dPointEquiv 1 (χ.onPoints x) 0) hzw
  rw [dLaurentCharacter_apply, dLaurentCharacter_apply] at hv
  have hx : dPointEquiv n x = Pi.mulSingle j a :=
    (dPointEquiv n).apply_symm_apply _
  have hv' : a ^ z j = a ^ w j := by
    simpa [hx, Pi.mulSingle_apply] using hv
  apply ha
  rw [zpow_sub, mul_inv_eq_one]
  exact hv'

end Theory.AlgebraicGroup
