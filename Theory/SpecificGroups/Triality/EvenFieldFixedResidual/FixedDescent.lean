module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.Carrier
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.Restriction
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.SubfieldLifts
/-!
# Canonical coefficient-fixed triality descent

For n = 2m > 0, first transport the original carrier's coefficient fixed
subgroup through its elementary central quotient to the inverse half twist.
The actual pinned arm swap changes that twist to the forward half twist.
The smaller-field entrywise embedding restricts to an equivalence: uniqueness
of the split Bruhat coordinates supplies an actual lift of each fixed matrix
in the smaller root-generated split group. Finally use the smaller carrier's
proved elementary central quotient.

The construction retains m = 1 and requires no simplicity or perfectness
assumption for either carrier. The original conditional assembly is retained;
`coefficientFixedEquivSmaller` discharges its lift premise using `SubfieldLifts`.
It supplies the canonical fixed-group identification required by the field
case of 16.1.4(4); normalization of a general field involution and passage
to the two-residual belong to the parent assembly.

Source: Aschbacher–Smith, Notation 16.1.3 and Lemma 16.1.4(4), printed p.1171
(`refs/quasithin.pdf`); GLS3 §§2.2 and 2.5–2.6
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.EvenField
open OuterOdd ConcreteBruhat.FixedDescent

/-- Canonical coefficient descent assembled from actual smaller-field split-group
lifts. The remaining premise is a root-generated-group descent statement,
not an assumption of the desired carrier equivalence. -/
def coefficientFixedEquivSmallerOfSplitLifts (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (hlift : ∀ x : SplitGroup (binaryParameters n hn), forwardGraphHalf n hn m x = x →
      ∃ y : SplitGroup (binaryParameters m hm), halfSplitMap n hn m hm hnm y = x) :
    (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m))).fixedSubgroup ≃*
      BinaryCarrier m hm :=
  (carrierCoefficientFixedEquivInverseGraph n hn m hnm).trans
    ((inverseGraphFixedEquivForward n hn m).trans
      ((halfFixedEquivOfSplitLifts n hn m hm hnm hlift).symm.trans
        (carrierFixedEquiv (binaryParameters m hm) rfl).symm))

/-- The fixed subgroup of the canonical coefficient involution is the genuine
smaller triality carrier. The split-group lifts, inverse-diagram comparison,
elementary subgroups and their own central quotients are all discharged.
This includes `m = 1`, with no simplicity or perfectness assumptions. -/
def coefficientFixedEquivSmaller (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m) :
    (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m))).fixedSubgroup ≃*
      BinaryCarrier m hm :=
  coefficientFixedEquivSmallerOfSplitLifts n hn m hm hnm
    (halfSplitMap_lift_of_forwardGraphHalf_fixed n hn m hm hnm)

end Triality.Standard.EvenField
