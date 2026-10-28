module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.DiagramFixed
public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.Inputs

/-!
# Inversion coordinates fixed by triality

The literal D4 root permutation tables determine the inversion set of each of
its twelve diagram-fixed Weyl words. The three cubic diagram orbits contribute
GF(q³) parameters and the three singleton orbits contribute q-Frobenius-fixed
parameters. Restricting the proved Frobenius-coordinate equivalence to these
inversion sets gives q raised to the number of inverted positive D4 roots.
Their sum is the Borel-index polynomial. No group order or Sylow assertion is
used; identification with carrier cells is in the parent module.

Source: GLS3 2.3.5, 2.3.7–8 and §2.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
open scoped BigOperators
namespace Triality.Standard.ConcreteBruhat.FixedCellCount
open PositiveCoordinates
noncomputable section

private def positiveNumber : Fin 12 → Fin 24 := ![1,21,20,13,5,17,16,9,12,8,4,0]

private lemma positiveNumber_spec (i : Fin 12) : rootEnumeration (positiveNumber i) = rootIndex i := by
  fin_cases i <;> rfl

private def numbering : rootWeylGroup →* Equiv.Perm (Fin 24) :=
  rootEnumeration.symm.permCongrHom.toMonoidHom.comp rootWeylGroup.subtype

private lemma numbering_generator (i : Fin 4) :
    numbering (rootWeylGenerator i) = DiagramFixed.reflection i := by
  apply Equiv.ext
  intro r
  change rootEnumeration.symm ((typeDRootPairing 2).reflectionPerm
    (typeDSimpleRootIndex 2 i) (rootEnumeration r)) = reflectionTable i r
  rw [← rootEnumeration_reflectionTable, Equiv.symm_apply_apply]

private lemma representative_numbered (w : DihedralGroup 6) (r : Fin 24) :
    (rootRepresentative w).val (rootEnumeration r) =
      rootEnumeration (DiagramFixed.representativeTable w r) := by
  have h : numbering (rootRepresentative w) = DiagramFixed.representative w := by
    cases w <;> simp [rootRepresentative, DiagramFixed.representative, foldedRootReflection,
      map_mul, map_pow, numbering_generator, DiagramFixed.arm]
  have hh := congrFun (congrArg (fun e : Equiv.Perm (Fin 24) => (e : Fin 24 → Fin 24)) h) r
  change rootEnumeration.symm ((rootRepresentative w).val (rootEnumeration r)) = _ at hh
  exact (rootEnumeration.apply_symm_apply _).symm.trans
    (congrArg rootEnumeration (hh.trans (DiagramFixed.representative_apply w r)))

private lemma positive_number_iff (r : Fin 24) :
    (typeDRootPairing_base 2).IsPos (rootEnumeration r) ↔ r.val % 4 < 2 := by
  rw [← show rootEnumeration r ∈ {r | (typeDRootPairing_base 2).IsPos r} ↔
    (typeDRootPairing_base 2).IsPos (rootEnumeration r) from Iff.rfl,
    ← range_rootIndex]
  change (∃ i, rootIndex i = rootEnumeration r) ↔ _
  simp only [← positiveNumber_spec, Equiv.apply_eq_iff_eq]
  revert r
  decide +kernel

/-- The literal root action sends this positive root to a negative root. -/
private def inverted (w : DihedralGroup 6) (i : Fin 12) : Bool :=
  decide (2 ≤ (DiagramFixed.representativeTable w (positiveNumber i)).val % 4)

private lemma inverted_iff (w : DihedralGroup 6) (i : Fin 12) :
    inverted w i = true ↔ ¬ (typeDRootPairing_base 2).IsPos
      ((rootRepresentative w).val (rootIndex i)) := by
  rw [← positiveNumber_spec, representative_numbered, positive_number_iff]
  simp only [inverted, decide_eq_true_eq, not_lt]

/-- Representatives of the three cubic and three singleton diagram orbits. -/
private def triplePosition : Fin 3 → Fin 12 := ![0,4,7]
private def singlePosition : Fin 3 → Fin 12 := ![3,10,11]

def inversionCount (w : DihedralGroup 6) : ℕ :=
  ∑ i : Fin 12, if inverted w i then 1 else 0

private def tripleCount (w : DihedralGroup 6) : ℕ :=
  Fintype.card {j : Fin 3 // inverted w (triplePosition j) = true}
private def singleCount (w : DihedralGroup 6) : ℕ :=
  Fintype.card {j : Fin 3 // inverted w (singlePosition j) = true}

private lemma inversionCount_orbits (w : DihedralGroup 6) :
    inversionCount w = 3 * tripleCount w + singleCount w := by
  revert w
  decide +kernel

lemma inversionCount_table (w : DihedralGroup 6) : inversionCount w =
    match w with
    | .r i => ![0,4,8,12,8,4] i
    | .sr i => ![3,1,5,9,11,7] i := by
  revert w
  decide +kernel

private lemma supported_iff (P : Parameters) (w : DihedralGroup 6) (a : Coordinates P) :
    SplitNormalForm.Supported P (rootRepresentative w) a ↔
      ∀ i, inverted w i = false → a i = 0 := by
  have hi (i) : inverted w i = false ↔
      (typeDRootPairing_base 2).IsPos ((rootRepresentative w).val (rootIndex i)) := by
    simpa only [Bool.not_eq_true, not_not] using not_congr (inverted_iff w i)
  simp only [SplitNormalForm.Supported, hi]

private lemma inverted_triples (w : DihedralGroup 6) :
    inverted w 1 = inverted w 0 ∧ inverted w 2 = inverted w 0 ∧
    inverted w 5 = inverted w 4 ∧ inverted w 6 = inverted w 4 ∧
    inverted w 8 = inverted w 7 ∧ inverted w 9 = inverted w 7 := by
  revert w
  decide +kernel

private lemma supported_expand_iff (P : Parameters) (w : DihedralGroup 6) (a : OrbitParameters P) :
    SplitNormalForm.Supported P (rootRepresentative w) (expand P a) ↔
      (∀ j, inverted w (triplePosition j) = false → a.1 j = 0) ∧
      (∀ j, inverted w (singlePosition j) = false → a.2 j = 0) := by
  rw [supported_iff]
  constructor
  · intro h
    constructor
    · intro j hj
      have hh := h (triplePosition j) hj
      fin_cases j <;> exact hh
    · intro j hj
      apply Subtype.ext
      have hh := h (singlePosition j) hj
      fin_cases j <;> exact hh
  · rintro ⟨ht, hs⟩ i hi
    have h := inverted_triples w
    have ht0 := ht 0
    have ht1 := ht 1
    have ht2 := ht 2
    have hs0 := congrArg (fun x : fixedField P => (x : ExtensionField P)) ∘ hs 0
    have hs1 := congrArg (fun x : fixedField P => (x : ExtensionField P)) ∘ hs 1
    have hs2 := congrArg (fun x : fixedField P => (x : ExtensionField P)) ∘ hs 2
    dsimp [triplePosition, singlePosition] at ht0 ht1 ht2 hs0 hs1 hs2
    fin_cases i <;> simp_all [expand, -fieldFrobenius_apply]

private def zeroOutsideEquiv (K : Type*) [Zero K] (p : Fin 3 → Bool) :
    ({j : Fin 3 // p j = true} → K) ≃ {a : Fin 3 → K // ∀ j, p j = false → a j = 0} where
  toFun a := ⟨fun j => if h : p j = true then a ⟨j, h⟩ else 0,
    by intro j hj; simp [hj]⟩
  invFun a j := a.val j.val
  left_inv a := by funext j; simp [j.property]
  right_inv a := by
    apply Subtype.ext
    funext j
    change (if h : p j = true then a.val j else 0) = a.val j
    split_ifs with h
    · rfl
    · exact (a.property j (by simpa using h)).symm

/-- Fixed tuples with the exact inversion support, using the genuine Frobenius. -/
abbrev FixedSupported (P : Parameters) (w : DihedralGroup 6) :=
  {a : FixedCoordinates P // SplitNormalForm.Supported P (rootRepresentative w) a.val}

/-- Independent extension and fixed-field parameters on the inverted diagram orbits. -/
private abbrev CellParameters (P : Parameters) (w : DihedralGroup 6) :=
  ({j : Fin 3 // inverted w (triplePosition j) = true} → ExtensionField P) ×
  ({j : Fin 3 // inverted w (singlePosition j) = true} → fixedField P)

private def cellParametersEquiv (P : Parameters) (w : DihedralGroup 6) :
    CellParameters P w ≃ FixedSupported P w :=
  ((Equiv.prodCongr (zeroOutsideEquiv (ExtensionField P) _)
      (zeroOutsideEquiv (fixedField P) _)).trans Equiv.subtypeProdEquivProd.symm).trans
    ((fixedCoordinatesEquiv P).subtypeEquiv (fun a => (supported_expand_iff P w a).symm))

theorem card_fixedSupported (P : Parameters) (w : DihedralGroup 6) :
    Nat.card (FixedSupported P w) = P.q ^ inversionCount w := by
  rw [← Nat.card_congr (cellParametersEquiv P w), Nat.card_prod,
    Nat.card_fun, Nat.card_fun, card_extensionField, card_fixedField,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← pow_mul, ← pow_add]
  rw [inversionCount_orbits]
  rfl

/-- The exponent counts the positive D4 roots inverted by the actual Weyl word. -/
theorem inversionCount_eq_card (w : DihedralGroup 6) :
    inversionCount w = Nat.card {i : Fin 12 //
      ¬ (typeDRootPairing_base 2).IsPos ((rootRepresentative w).val (rootIndex i))} := by
  rw [← Nat.card_congr (Equiv.subtypeEquivRight (inverted_iff w))]
  rw [Nat.card_eq_fintype_card]
  revert w
  decide +kernel

/-- The literal simultaneous support and Frobenius equations have q^ℓ solutions. -/
theorem card_supported_twist (P : Parameters) (w : DihedralGroup 6) :
    Nat.card {a : Coordinates P // SplitNormalForm.Supported P (rootRepresentative w) a ∧
      twist P a = a} = P.q ^ inversionCount w := by
  have e : FixedSupported P w ≃ {a : Coordinates P //
      SplitNormalForm.Supported P (rootRepresentative w) a ∧ twist P a = a} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
      (Equiv.subtypeEquivRight (fun _ => and_comm))
  rw [← Nat.card_congr e, card_fixedSupported]

/-- The weighted Poincaré polynomial of the twelve actual inversion sets. -/
theorem sum_inversion_powers (q : ℕ) :
    (∑ w : DihedralGroup 6, q ^ inversionCount w) =
      (q ^ 3 + 1) * (q + 1) * (q ^ 8 + q ^ 4 + 1) := by
  rw [← (DihedralGroup.equivSum : DihedralGroup 6 ≃ ZMod 6 ⊕ ZMod 6).symm.sum_comp]
  simp only [Fintype.sum_sum_type, DihedralGroup.equivSum, Equiv.symm_mk,
    inversionCount_table]
  change (∑ i : Fin 6, q ^ (![0,4,8,12,8,4] i)) +
    (∑ i : Fin 6, q ^ (![3,1,5,9,11,7] i)) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, pow_zero, pow_one, add_zero]
  ring

end
end Triality.Standard.ConcreteBruhat.FixedCellCount
