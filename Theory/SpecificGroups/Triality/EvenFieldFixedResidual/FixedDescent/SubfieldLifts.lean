module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.SubfieldLifts.NormalForm
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.Restriction

/-!
# Actual subfield lifts for the triality half twist

When n = 2m, the published embedding of GF(2^(3m)) into GF(2^(3n))
has image exactly the fixed field of the coefficient involution. The unique
split Bruhat form descends any coefficient-fixed split matrix as a product
of smaller-field root and coroot words. Cubing the forward half twist gives
that coefficient involution, so the same descent applies to every half-twist
fixed matrix, including m = 1.

The final theorem applies these lifts to the literal `halfFixedMap`, proving
its surjectivity. Inverse-diagram comparison and the elementary central
quotients remain with the parent carrier assembly. No simplicity or
perfectness assumption is needed for either carrier.

Source: Aschbacher–Smith, Notation 16.1.3 and Lemma 16.1.4(4), printed
p.1171 (`refs/quasithin.pdf`); GLS3 §§2.2 and 2.5–2.6, with the split
Bruhat coordinates of 2.3.5 and 2.3.8
(`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
namespace Triality.Standard.EvenField

/-- A coefficient-fixed split matrix lifts to the smaller root-generated group. -/
theorem halfSplitMap_lift_of_coefficient_fixed (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (x : SplitGroup (binaryParameters n hn))
    (hx : splitFrobenius n hn (3*m) x = x) :
    ∃ y : SplitGroup (binaryParameters m hm), halfSplitMap n hn m hm hnm y = x := by
  exact SubfieldLifts.split_lift_of_fixed n hn (binaryParameters m hm)
    (halfFieldEmbedding n hn m hm hnm) (coefficientFrobenius n hn (3*m))
    (fun t ht => (halfFieldEmbedding_range n hn m hm hnm t).mpr ht) x hx

/-- Every forward half-twist fixed matrix has an actual smaller-field split-group lift. -/
theorem halfSplitMap_lift_of_forwardGraphHalf_fixed (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (x : SplitGroup (binaryParameters n hn)) (hx : forwardGraphHalf n hn m x = x) :
    ∃ y : SplitGroup (binaryParameters m hm), halfSplitMap n hn m hm hnm y = x :=
  halfSplitMap_lift_of_coefficient_fixed n hn m hm hnm x
    (forwardGraphHalf_fixed_coefficient n hn m x hx)

/-- The lift theorem discharges the precise premise of the fixed-group restriction. -/
theorem halfFixedMap_surjective (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m) :
    Function.Surjective (halfFixedMap n hn m hm hnm) :=
  halfFixedMap_surjective_of_split_lifts n hn m hm hnm
    (halfSplitMap_lift_of_forwardGraphHalf_fixed n hn m hm hnm)

end Triality.Standard.EvenField
