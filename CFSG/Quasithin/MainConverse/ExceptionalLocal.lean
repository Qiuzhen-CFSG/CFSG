module

public import CFSG.Quasithin.MainConverse.ExceptionalLocal.SmallOrders
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Even.OddRank
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Even
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.Triality
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.Tits

/-!
# Exceptional-family local calculations for the converse

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 0.1.2(1,4), printed p.4, repeated on p.482.
The intended branches are G₂(2^f) for f ≥ 2, G₂(3), the actual commutator
of G₂(2), genuine graph-field triality ³D₄(2^f) for f ≥ 1, and the Tits group.

All five branches satisfy QT and E. The even-field G₂ and genuine triality
calculations cover arbitrary two-local normalizers by conjugate parabolics,
bound their odd-prime ranks, and prove their intrinsic two-cores
self-centralizing. The small G₂ and Tits calculations supply their own
exhaustive local covers and rank bounds. Actual multiplicative equivalences
transport these conclusions to the classification model witnesses.

This module re-exports the small G₂ and Tits conclusions and supplies the
remaining field-order interfaces below, with the source parameter ranges.
No QT, E, local-coverage or proper-K premise is needed for these conclusions.
The final classification consumer supplies proper K as its induction hypothesis.
-/

namespace CFSG.Quasithin.MainConverse.ExceptionalLocal

/-- QT and E for every copy of G₂(2^f) in the source's range f ≥ 2.
The field witness identifies the actual split-octonion automorphism group. -/
public theorem g2_even_quasithin_evenCharacteristic
    {G : Type*} [Group G] [Finite G] {f : ℕ} (_hf : 2 ≤ f)
    (hG : ClassificationModels.IsG2At G (2 ^ f)) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  obtain ⟨hqt, heven⟩ := G2Even.quasithin_evenCharacteristic_of_card hcard
  exact ⟨Theory.GroupTheory.isQuasithin_of_equiv e.symm hqt,
    evenCharacteristic_of_model_equiv e heven⟩

/-- QT and E for every genuine graph-field triality group ³D₄(2^f), f ≥ 1.
The carrier retains the elementary fixed-point subgroup and its own center quotient. -/
public theorem triality_even_quasithin_evenCharacteristic
    {G : Type*} [Group G] [Finite G] {f : ℕ} (hf : 1 ≤ f)
    (hG : Triality.Standard.IsTrialityGroupAt (2 ^ f) G) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  TrialityLocal.quasithin_and_evenCharacteristic_of_isTrialityGroupAt f hf hG

end CFSG.Quasithin.MainConverse.ExceptionalLocal
