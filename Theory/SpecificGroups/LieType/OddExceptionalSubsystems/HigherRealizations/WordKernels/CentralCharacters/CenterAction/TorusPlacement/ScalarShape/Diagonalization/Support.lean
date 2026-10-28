module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.Operators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.FixedRows
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.Diagonalization.Grading

/-!
# Cartan commutators and entry support for central evaluated E6 words

The first step in the diagonalization argument is integral.  Commutation with
the positive and negative simple coefficients gives commutation with their
`e`--`f` commutator, hence with the diagonal Cartan matrix whose root entries
are the integral pairings.  No division by three occurs in this reduction.

A nonzero entry consequently has equal six Cartan weights in the coefficient
field. The integral complementary gradings from `Grading` also agree, by actual
word membership. The final two support theorems combine these restrictions.

These reductions do not yet prove diagonality. The remaining argument must
separate root coordinates within a grade and exclude off-diagonal Cartan
entries, including possible characteristic-three shears. Ambient commutation
alone cannot supply the latter conclusion.

Sources: GLS3 §§1.12.5–6 and 2.6.2; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open RootPairing.SimpleGeckGroup
noncomputable section

namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape

attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

section Cartan

variable {ι R M N F : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι] [Field F]

private theorem commute_cartan_of_coefficients (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)
    (i : b.support)
    (hc : Commute A ((simpleFamily (b := b)).coefficient (true, i) 1))
    (hf : Commute A ((simpleFamily (b := b)).coefficient (false, i) 1)) :
    Commute A (Matrix.diagonal (Sum.elim (fun _ : b.support => (0 : F))
      (fun r => (P.pairingIn ℤ r i : F)))) := by
  let j : b.support := i
  have he' : Commute A (eMatrix (P := P) j |>.map (Int.castRingHom F)) := by
    simpa [IntegralCubicFamily.coefficient, simpleFamily, eDividedPower,
      eDividedPower_one, Matrix.map_zero] using hc
  have hf0 : Commute A ((fDividedPower (P := P) j 1).map (Int.castRingHom F)) := by
    simpa [IntegralCubicFamily.coefficient, simpleFamily, Matrix.map_zero] using hf
  have hf' : Commute A (fMatrix (P := P) j |>.map (Int.castRingHom F)) := by
    simpa only [fDividedPower_one] using hf0
  have hcomm : Commute A ((eMatrix (P := P) j * fMatrix (P := P) j -
      fMatrix (P := P) j * eMatrix (P := P) j).map (Int.castRingHom F)) := by
    rw [Matrix.map_sub (Int.castRingHom F) (by intros; simp), Matrix.map_mul, Matrix.map_mul]
    change A * ((eMatrix (P := P) j).map (Int.castRingHom F) *
      (fMatrix (P := P) j).map (Int.castRingHom F) -
      (fMatrix (P := P) j).map (Int.castRingHom F) *
      (eMatrix (P := P) j).map (Int.castRingHom F)) = _
    rw [mul_sub, sub_mul]
    change A * ((eMatrix (P := P) j).map (Int.castRingHom F) *
        (fMatrix (P := P) j).map (Int.castRingHom F)) -
      A * ((fMatrix (P := P) j).map (Int.castRingHom F) *
        (eMatrix (P := P) j).map (Int.castRingHom F)) = _
    calc
      A * ((eMatrix (P := P) j).map (Int.castRingHom F) *
          (fMatrix (P := P) j).map (Int.castRingHom F)) -
          A * ((fMatrix (P := P) j).map (Int.castRingHom F) *
            (eMatrix (P := P) j).map (Int.castRingHom F)) =
        (A * (eMatrix (P := P) j).map (Int.castRingHom F)) *
            (fMatrix (P := P) j).map (Int.castRingHom F) -
          (A * (fMatrix (P := P) j).map (Int.castRingHom F)) *
            (eMatrix (P := P) j).map (Int.castRingHom F) := by
        simp only [mul_assoc]
      _ = ((eMatrix (P := P) j).map (Int.castRingHom F) * A) *
            (fMatrix (P := P) j).map (Int.castRingHom F) -
          ((fMatrix (P := P) j).map (Int.castRingHom F) * A) *
            (eMatrix (P := P) j).map (Int.castRingHom F) := by
        rw [he'.eq, hf'.eq]
      _ = ((eMatrix (P := P) j).map (Int.castRingHom F) *
            (fMatrix (P := P) j).map (Int.castRingHom F)) * A -
          ((fMatrix (P := P) j).map (Int.castRingHom F) *
            (eMatrix (P := P) j).map (Int.castRingHom F)) * A := by
        simp only [mul_assoc]
        rw [hf'.eq, he'.eq]
      _ = _ := by rfl
  have hlie := RootPairing.GeckConstruction.lie_e_f_same (P := P) (b := b) j
  let hInt : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
    Matrix.diagonal (Sum.elim (fun _ : b.support => 0) (fun r => P.pairingIn ℤ r j))
  have hlie' : eMatrix (P := P) j * fMatrix (P := P) j -
      fMatrix (P := P) j * eMatrix (P := P) j = hInt := by
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ R)
    change (eMatrix (P := P) j * fMatrix (P := P) j -
      fMatrix (P := P) j * eMatrix (P := P) j).map (algebraMap ℤ R) = hInt.map (algebraMap ℤ R)
    rw [Matrix.map_sub (algebraMap ℤ R) (by intros; simp), Matrix.map_mul, Matrix.map_mul]
    change (eMatrix (P := P) j).map (algebraMap ℤ R) *
      (fMatrix (P := P) j).map (algebraMap ℤ R) -
      (fMatrix (P := P) j).map (algebraMap ℤ R) *
      (eMatrix (P := P) j).map (algebraMap ℤ R) = _
    rw [map_eMatrix, map_fMatrix]
    change RootPairing.GeckConstruction.e j * RootPairing.GeckConstruction.f j -
      RootPairing.GeckConstruction.f j * RootPairing.GeckConstruction.e j =
      (Matrix.diagonal (Sum.elim (fun _ : b.support => 0)
        (fun r => P.pairingIn ℤ r j))).map (algebraMap ℤ R)
    have hmap : (Matrix.diagonal (Sum.elim (fun _ : b.support => 0)
        (fun r => P.pairingIn ℤ r j))).map (algebraMap ℤ R) =
        Matrix.diagonal (Sum.elim (fun _ : b.support => (0 : R))
          (fun r => (P.pairingIn ℤ r j : R))) := by
      ext x y
      cases x <;> cases y <;> simp [Matrix.diagonal_apply]
    rw [hmap]
    rw [RootPairing.GeckConstruction.h_eq_diagonal] at hlie
    have hz : (0 : b.support → R) = (fun _ => 0) := by
      funext x
      rfl
    rw [hz] at hlie
    simpa [Ring.lie_def] using hlie
  rw [hlie'] at hcomm
  have hmap : (Matrix.diagonal (Sum.elim (fun _ : b.support => 0)
      (fun r => P.pairingIn ℤ r j))).map (Int.castRingHom F) =
      Matrix.diagonal (Sum.elim (fun _ : b.support => (0 : F))
        (fun r => (P.pairingIn ℤ r j : F))) := by
    ext x y
    cases x <;> cases y <;> simp [Matrix.diagonal_apply]
  rw [hmap] at hcomm
  exact hcomm

end Cartan

/-- A central E7 six-node value commutes with every integral E6 Cartan diagonal. -/
theorem e7Six_commutes_cartan (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (w : SixNodeWord F) (hc : ∀ z, Commute (e7Six F w) (e7Six F z)) (i : Fin 6) :
    Commute (e7Six F w).val.val
      (Matrix.diagonal (Sum.elim (fun _ : typeE7RootPairing_base.support => (0 : F))
        (fun r => (typeE7RootPairing.pairingIn ℤ r (e7Node i) : F)))) := by
  exact commute_cartan_of_coefficients _ _
    ((e7Six_central_iff_operators F hodd w).mp hc true i)
    ((e7Six_central_iff_operators F hodd w).mp hc false i)

/-- A central E8 six-node value commutes with every integral E6 Cartan diagonal. -/
theorem e8Six_commutes_cartan (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (w : SixNodeWord F) (hc : ∀ z, Commute (e8Six F w) (e8Six F z)) (i : Fin 6) :
    Commute (e8Six F w).val.val
      (Matrix.diagonal (Sum.elim (fun _ : typeE8RootPairing_base.support => (0 : F))
        (fun r => (typeE8RootPairing.pairingIn ℤ r (e8Node i) : F)))) := by
  exact commute_cartan_of_coefficients _ _
    ((e8Six_central_iff_operators F hodd w).mp hc true i)
    ((e8Six_central_iff_operators F hodd w).mp hc false i)

/-- A nonzero entry of a matrix commuting with a diagonal equates its two weights. -/
theorem weight_eq_of_commute_diagonal {n F : Type*} [Fintype n] [DecidableEq n] [Field F]
    (A : Matrix n n F) (d : n → F) (hc : Commute A (Matrix.diagonal d))
    (r c : n) (h : A r c ≠ 0) : d r = d c := by
  have he := congrArg (fun B : Matrix n n F => B r c) hc.eq
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  exact (mul_left_cancel₀ h (he.trans (mul_comm _ _))).symm


/-- Every nonzero entry of a central E7 word has equal six Cartan weights in the field. -/
theorem e7Six_entry_weights (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (w : SixNodeWord F) (hc : ∀ z, Commute (e7Six F w) (e7Six F z))
    (r c : typeE7RootPairing_base.support ⊕ typeE7Roots)
    (h : (e7Six F w).val.val r c ≠ 0) (i : Fin 6) :
    (chevalleyBasisWeight (P := typeE7RootPairing) r (e7Node i) : F) =
      (chevalleyBasisWeight (P := typeE7RootPairing) c (e7Node i) : F) := by
  have he := weight_eq_of_commute_diagonal _ _ (e7Six_commutes_cartan F hodd w hc i) r c h
  cases r <;> cases c
  · rfl
  · simpa [chevalleyBasisWeight] using he
  · simpa [chevalleyBasisWeight] using he
  · exact he

/-- Every nonzero entry of a central E8 word has equal six Cartan weights in the field. -/
theorem e8Six_entry_weights (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (w : SixNodeWord F) (hc : ∀ z, Commute (e8Six F w) (e8Six F z))
    (r c : typeE8RootPairing_base.support ⊕ typeE8Roots)
    (h : (e8Six F w).val.val r c ≠ 0) (i : Fin 6) :
    (chevalleyBasisWeight (P := typeE8RootPairing) r (e8Node i) : F) =
      (chevalleyBasisWeight (P := typeE8RootPairing) c (e8Node i) : F) := by
  have he := weight_eq_of_commute_diagonal _ _ (e8Six_commutes_cartan F hodd w hc i) r c h
  cases r <;> cases c
  · rfl
  · simpa [chevalleyBasisWeight] using he
  · simpa [chevalleyBasisWeight] using he
  · exact he


/-- Nonzero entries of a central E7 word agree both in the integral complementary
grade and in all six Cartan weights after specialization. -/
theorem e7Six_entry_support (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (w : SixNodeWord F) (hc : ∀ z, Commute (e7Six F w) (e7Six F z))
    (r c : typeE7RootPairing_base.support ⊕ typeE7Roots)
    (h : (e7Six F w).val.val r c ≠ 0) :
    e7ComplementGrade r = e7ComplementGrade c ∧
      ∀ i : Fin 6, (chevalleyBasisWeight (P := typeE7RootPairing) r (e7Node i) : F) =
        (chevalleyBasisWeight (P := typeE7RootPairing) c (e7Node i) : F) := by
  refine ⟨?_, e7Six_entry_weights F hodd w hc r c h⟩
  by_contra hn
  exact h (e7Six_entry_zero_of_complementGrade F w r c hn)

/-- Nonzero entries of a central E8 word agree both in the integral complementary
grade and in all six Cartan weights after specialization. -/
theorem e8Six_entry_support (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (w : SixNodeWord F) (hc : ∀ z, Commute (e8Six F w) (e8Six F z))
    (r c : typeE8RootPairing_base.support ⊕ typeE8Roots)
    (h : (e8Six F w).val.val r c ≠ 0) :
    e8ComplementGrade r = e8ComplementGrade c ∧
      ∀ i : Fin 6, (chevalleyBasisWeight (P := typeE8RootPairing) r (e8Node i) : F) =
        (chevalleyBasisWeight (P := typeE8RootPairing) c (e8Node i) : F) := by
  refine ⟨?_, e8Six_entry_weights F hodd w hc r c h⟩
  by_contra hn
  exact h (e8Six_entry_zero_of_complementGrade F w r c hn)

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
