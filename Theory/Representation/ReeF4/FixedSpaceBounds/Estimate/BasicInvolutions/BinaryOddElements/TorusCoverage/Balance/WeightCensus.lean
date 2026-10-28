module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance.Actions
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance.WeightCensus.Roots

/-!
# Torus ranks on the short F4 ideal and its quotient

The actual short ideal has twenty-four distinct short-root weights and two
zero-weight Cartan coordinates. The genuine quotient has twenty-four distinct
long-root weights and two zero-weight Cartan coordinates. The root-table
bijections identify every multiplicity, and the positive-coroot diagonal
formula converts the ranks into counts of characters different from one.

For the quotient, the fixed coordinate duality is only a reindexing of the
quotient action already certified in `Balance.Actions`. No invariance of the
long-coordinate complement is needed. The two final formulas discharge exactly
the premises of `Balance.balance_of_torus_rank_counts`; they hold for arbitrary
torus parameters, without a Ree fixed-point or conjugacy hypothesis.

Source: the fixed-space argument in Guralnick--Malle II, Lemma 8.8 (internal
p.57), and the F4 root conventions of GLS3, Sections 1.14 and 2.8.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
open ReeF4.BinaryDegree.ExceptionalTensor ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
open scoped Classical Matrix
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance
open WeightCensus
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
variable {F : Type*} [Field F]

private theorem shortCartan_card :
    Fintype.card {i : typeF4RootPairing_base.support // IsShortRoot i.val} = 2 := by
  have e := Equiv.subtypeEquiv (p := fun i : Fin 4 => 2 ≤ i.val)
    (q := fun i : typeF4RootPairing_base.support => IsShortRoot i.val)
    typeF4RootPairing_baseEquiv (fun i => (ShortOperators.isShortRoot_simple i).symm)
  exact (Fintype.card_congr e).symm.trans (by decide)

/-- Both actions have dimension 26: 24 root coordinates and two Cartan coordinates. -/
theorem shortIndex_card : Fintype.card ShortIndex = 26 := by
  rw [Fintype.card_congr (Equiv.subtypeSum (p := IsShortCoordinate)), Fintype.card_sum]
  change Fintype.card {i : typeF4RootPairing_base.support // IsShortRoot i.val} +
    Fintype.card {r : typeF4Roots // IsShortRoot r} = 26
  rw [shortCartan_card, ← Fintype.card_congr shortRootEquiv, Fintype.card_fin]

private theorem cartan_weight (j : typeF4RootPairing_base.support) :
    F4Chevalley.basisWeight (Sum.inl j) = 0 := rfl

private theorem character_zero (t : Fin 4 → Fˣ) : corootCharacter t 0 = 1 := by
  simp only [corootCharacter, Pi.zero_apply, zpow_zero, mul_one]

private def movingCoordinateEquiv (p : Coordinate → Prop) (W : Fin 24 → CorootWeight)
    (e : Fin 24 ≃ {r : typeF4Roots // p (Sum.inr r)})
    (he : ∀ n, F4Chevalley.basisWeight (Sum.inr (e n).val) = W n)
    (t : Fin 4 → Fˣ) :
    {n : Fin 24 // corootCharacter t (W n) ≠ 1} ≃
      {i : {i : Coordinate // p i} // corootCharacter t (F4Chevalley.basisWeight i.val) ≠ 1} := by
  let f : {n : Fin 24 // corootCharacter t (W n) ≠ 1} →
      {i : {i : Coordinate // p i} // corootCharacter t (F4Chevalley.basisWeight i.val) ≠ 1} :=
    fun n => ⟨⟨Sum.inr (e n.val).val, (e n.val).property⟩, by
      simpa only [he] using n.property⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro n m h
    apply Subtype.ext
    apply e.injective
    apply Subtype.ext
    exact Sum.inr.inj (congrArg (fun i => i.val.val) h)
  · rintro ⟨⟨i, hi⟩, hm⟩
    cases i with
    | inl j => exact (hm (by rw [cartan_weight, character_zero])).elim
    | inr r =>
      obtain ⟨n, hn⟩ := e.surjective ⟨r, hi⟩
      have hnmove : corootCharacter t (W n) ≠ 1 := by
        rw [← he n, hn]
        exact hm
      refine ⟨⟨n, hnmove⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg Sum.inr (congrArg Subtype.val hn)

private theorem diagonal_rank (ι : Type*) [Fintype ι] [DecidableEq ι]
    (w : ι → CorootWeight) (t : Fin 4 → Fˣ) :
    ((Matrix.diagonal (fun i => (corootCharacter t (w i) : F))) - 1).rank =
      Fintype.card {i : ι // corootCharacter t (w i) ≠ 1} := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.rank_diagonal]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  change ((corootCharacter t (w i) : F) - 1 ≠ 0) ↔ corootCharacter t (w i) ≠ 1
  rw [sub_ne_zero]
  exact not_congr (Units.val_eq_one (a := corootCharacter t (w i)))

private theorem rank_count (p : Coordinate → Prop) (W : Fin 24 → CorootWeight)
    (e : Fin 24 ≃ {r : typeF4Roots // p (Sum.inr r)})
    (he : ∀ n, F4Chevalley.basisWeight (Sum.inr (e n).val) = W n)
    (t : Fin 4 → Fˣ) :
    ((Matrix.diagonal (fun i : {i : Coordinate // p i} =>
      (corootCharacter t (F4Chevalley.basisWeight i.val) : F))) - 1).rank +
      fixedWeightCount W t = 24 := by
  rw [diagonal_rank]
  rw [← Fintype.card_congr (movingCoordinateEquiv p W e he t)]
  rw [Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 24)))
    (fun n => corootCharacter t (W n) = 1)
  change _ + _ = 24 at h
  exact (Nat.add_comm _ _).trans h

private abbrev LongIndex := {i : Coordinate // ¬IsShortCoordinate i}

private def dualIndexEquiv : ShortIndex ≃ LongIndex :=
  Equiv.subtypeEquiv coordinatePermutation (fun i => by
    rw [coordinatePermutation_short_iff, not_not])

variable [IsAlgClosed F] [CharP F 2]

/-- The 24 short-root characters, with two fixed Cartan coordinates, give the
exact displacement rank on the short ideal. -/
theorem short_torus_rank_count (t : Fin 4 → Fˣ) :
    (shortAction (corootTorusElement t) - 1).rank +
      fixedWeightCount EndNode.endOrbitWeight t = 24 := by
  change (shortBlock (pointMatrix (corootTorusElement t) : Matrix Coordinate Coordinate F) - 1).rank + _ = _
  rw [pointMatrix_coroot_diagonal]
  simp only [shortBlock, Matrix.submatrix_diagonal _ _ Subtype.val_injective]
  exact rank_count IsShortCoordinate EndNode.endOrbitWeight shortRootEquiv shortRootEquiv_weight t

/-- The quotient has the 24 long-root characters and two fixed Cartan
coordinates; duality only indexes this genuine quotient action. -/
theorem quotient_torus_rank_count (t : Fin 4 → Fˣ) :
    (quotientAction (corootTorusElement t) - 1).rank +
      fixedWeightCount longOrbitWeight t = 24 := by
  change (quotientBlock (pointMatrix (corootTorusElement t) : Matrix Coordinate Coordinate F) - 1).rank + _ = _
  rw [pointMatrix_coroot_diagonal]
  rw [quotientBlock, Matrix.submatrix_diagonal _
    (fun i : ShortIndex => coordinatePermutation i.val)
    (coordinatePermutation.injective.comp Subtype.val_injective)]
  change ((Matrix.diagonal (fun i : ShortIndex =>
    (corootCharacter t (F4Chevalley.basisWeight (coordinatePermutation i.val)) : F))) - 1).rank +
      fixedWeightCount longOrbitWeight t = 24
  rw [diagonal_rank]
  have e : {i : ShortIndex // corootCharacter t
      (F4Chevalley.basisWeight (coordinatePermutation i.val)) ≠ 1} ≃
      {i : LongIndex // corootCharacter t (F4Chevalley.basisWeight i.val) ≠ 1} :=
    Equiv.subtypeEquiv dualIndexEquiv (fun _ => Iff.rfl)
  rw [Fintype.card_congr e]
  have h := rank_count (fun i => ¬IsShortCoordinate i) longOrbitWeight
    longRootEquiv longRootEquiv_weight t
  rw [diagonal_rank] at h
  simpa only [Fintype.card_eq_nat_card] using h

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance
