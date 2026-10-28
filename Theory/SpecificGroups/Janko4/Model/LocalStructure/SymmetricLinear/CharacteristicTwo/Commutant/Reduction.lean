module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Checks

/-!
# Exhaustive reduction of the max4 commutant to packed identities

Commutation transports the images of the four last coordinate rows along
all certified orbit paths. A checked inverse recovers every matrix entry.
The selected commutator equations vanish on those images, as do their
checked combinations. The upper-entry certificates therefore prove the
required bound for every matrix, with no invertibility assumption.
Source: `CharacteristicTwo/source/README.md`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof
open GeneratorCertificates
open scoped Matrix

private lemma difference_zero : differences.get 0 = difference0 := rfl
private lemma column_zero : columns.get 0 = column0 := rfl

attribute [local irreducible] differences columns orbitRows inverseRows smallRows expressions
  expressionColumns parents factors equationPositions equationRows pivotRows pivotSources upperWitnesses
  difference0 column0

theorem difference_eq (hd : ∀ a, DifferenceCheck a) (a : Fin 11) :
    decodeRows (differences.get a) = decodeRows (Coordinates.conjugateRows.get a) + 1 := by
  funext i j
  change bit ((differences.get a).get i) j.val =
    bit ((Coordinates.conjugateRows.get a).get i) j.val + (1 : BinaryMatrix) i j
  rw [hd a i, bit_xor]
  congr 1
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem difference_commute (hd : ∀ a, DifferenceCheck a) (M : BinaryMatrix)
    (hM : ∀ a, Commute M (decodeRows (Coordinates.conjugateRows.get a))) (a : Fin 11) :
    Commute M (decodeRows (differences.get a)) := by
  rw [difference_eq hd]
  exact (hM a).add_right (Commute.one_right M)

def seedCoefficients (M : BinaryMatrix) : Fin 448 → ZMod 2 := fun t =>
  M (Fin.natAdd 108 ((@finProdFinEquiv 4 112).symm t).1) ((@finProdFinEquiv 4 112).symm t).2

theorem initial_image (hi : ∀ i, InitialCheck i) (M : BinaryMatrix) (i : Fin 4) :
    row (orbitRows.get (Fin.castLE (by decide) i)) ᵥ* M =
      evaluate (seedCoefficients M) (expressions.get (Fin.castLE (by decide) i)) := by
  rw [(hi i).1, row_unit, Matrix.single_vecMul, one_smul]
  funext j
  rw [evaluate, (hi i).2, ev_unit]
  simp only [seedCoefficients, Equiv.symm_apply_apply, Matrix.row_apply]

theorem orbit_images (hd : ∀ a, DifferenceCheck a) (hc : ∀ a, ColumnCheck a)
    (hi : ∀ i, InitialCheck i) (ho : ∀ i, OrbitCheck i)
    (M : BinaryMatrix)
    (hM : ∀ a, Commute M (decodeRows (Coordinates.conjugateRows.get a))) :
    ∀ i : Fin 112, row (orbitRows.get i) ᵥ* M =
      evaluate (seedCoefficients M) (expressions.get i) := by
  suffices ∀ n (hn : n < 112), row (orbitRows.get ⟨n, hn⟩) ᵥ* M =
      evaluate (seedCoefficients M) (expressions.get ⟨n, hn⟩) by
    intro i
    exact this i.val i.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    let i : Fin 112 := ⟨n, hn⟩
    by_cases hsmall : i.val < 4
    · exact initial_image hi M ⟨i.val, hsmall⟩
    · obtain ⟨hp, hr, he⟩ := ho i (by omega)
      rw [← hr, row_scan, commute_row _ _ (difference_commute hd M hM _),
        ih (parents.get i).val hp (parents.get i).isLt]
      apply evaluate_mul _ _ _ (columns.get (factors.get i)) _ _ he
      intro s t
      change (if ((columns.get (factors.get i)).get t).testBit s.val then 1 else 0) = _
      rw [hc]
      rfl

theorem scan_images (hc : ∀ j, ExpressionColumnCheck j)
    (M : BinaryMatrix) (c : Fin 448 → ZMod 2)
    (h : ∀ i, row (orbitRows.get i) ᵥ* M = evaluate c (expressions.get i))
    (r : ℕ) (j : Fin 112) :
    ev c (scan r (expressionColumns.get j).toList) =
      ((row r ᵥ* decodeRows orbitRows) ᵥ* M) j := by
  have hm : decodeRows orbitRows * M = fun i => evaluate c (expressions.get i) := by
    funext i
    exact h i
  rw [Matrix.vecMul_vecMul, hm, ev_scan]
  simp only [Matrix.vecMul, dotProduct, row, evaluate]
  apply Finset.sum_congr rfl
  intro k _
  rw [hc j k]

theorem equation_zero (hcols : ∀ a, ColumnCheck a)
    (hc : ∀ j, ExpressionColumnCheck j) (hs : ∀ i, SmallCheck i)
    (he : ∀ t, EquationCheck t)
    (M : BinaryMatrix) (c : Fin 448 → ZMod 2)
    (h : ∀ i, row (orbitRows.get i) ᵥ* M = evaluate c (expressions.get i))
    (hM : Commute M (decodeRows difference0)) (t : Fin 418) :
    ev c (equationRows.get t) = 0 := by
  let i := (equationPositions.get t).1
  let j := (equationPositions.get t).2
  have heq : equationRows.get t =
      scan (column0.get j) (expressions.get i).toList ^^^
        scan (smallRows.get i) (expressionColumns.get j).toList := he t
  rw [heq, ev_xor, scan_images hc M c h, ← row_scan, hs i, row_scan,
    commute_row M _ hM, h i]
  have hcol (k : Fin 112) : bit (column0.get j) k.val = decodeRows difference0 k j := by
    have hh := hcols 0 k j
    rw [column_zero, difference_zero] at hh
    simp only [bit, decodeRows, hh]
  have hl : ev c (scan (column0.get j) (expressions.get i).toList) =
      (evaluate c (expressions.get i) ᵥ* decodeRows difference0) j := by
    rw [ev_scan]
    simp only [Matrix.vecMul, dotProduct, evaluate, hcol, mul_comm]
  rw [hl, CharTwo.add_self_eq_zero]

theorem pivot_zero (hp : ∀ t, PivotCheck t) (c : Fin 448 → ZMod 2)
    (he : ∀ t, ev c (equationRows.get t) = 0) (t : Fin 418) :
    ev c (pivotRows.get t) = 0 := by
  rw [← hp t, ev_scan]
  simp only [he, mul_zero, Finset.sum_const_zero]

/-- Every hypothesis here is an explicit finite identity in the published data.
No assertion about a matrix is included in a certificate premise. -/
theorem lowerTriangular_of_checks
    (hd : ∀ a, DifferenceCheck a) (hcols : ∀ a, ColumnCheck a)
    (hc : ∀ j, ExpressionColumnCheck j) (hi : ∀ i, InitialCheck i)
    (ho : ∀ i, OrbitCheck i) (hinv : ∀ i, InverseCheck i)
    (hs : ∀ i, SmallCheck i) (he : ∀ t, EquationCheck t)
    (hp : ∀ t, PivotCheck t) (hu : ∀ i, UpperCheck i)
    (M : BinaryMatrix)
    (hM : ∀ a, Commute M (decodeRows (Coordinates.conjugateRows.get a))) :
    ∀ i j : Fin 112, i < j → M i j = 0 := by
  let c := seedCoefficients M
  have him := orbit_images hd hcols hi ho M hM
  have hcomm : Commute M (decodeRows difference0) := by
    simpa only [difference_zero] using difference_commute hd M hM 0
  have hz := pivot_zero hp c (equation_zero hcols hc hs he M c him hcomm)
  intro i j hij
  have hentry := scan_images hc M c him (inverseRows.get i) j
  rw [← row_scan, hinv i, row_unit, Matrix.single_vecMul, one_smul, Matrix.row_apply] at hentry
  rw [← hentry, hu i j hij, ev_scan]
  simp only [hz, mul_zero, Finset.sum_const_zero]

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof
