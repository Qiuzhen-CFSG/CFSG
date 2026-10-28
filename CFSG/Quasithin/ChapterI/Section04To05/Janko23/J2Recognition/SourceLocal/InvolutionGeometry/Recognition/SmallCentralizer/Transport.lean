module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.Contracts

/-!
# Transport of the small-centralizer calculation

Conjugation transports both the full centralizer and the literal Thompson
pair count between second-class representatives. If the local subgroup
X₁A₁ has order 48 and lies in one such centralizer, an order-48 assumption
at any other representative identifies that full centralizer with X₁A₁.
This justifies using the source's chosen representative for the pair count.

The local subgroup inclusion and its order remain inputs here; constructing
that subgroup requires the w = 2 geometry in §46.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.1, pp.259–260.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Conjugation gives an actual equivalence of the full centralizers. -/
theorem centralizer_card_conj {x y : G} (h : IsConj x y) :
    Nat.card (involutionCentralizer x) = Nat.card (involutionCentralizer y) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  have he : e x = y := hg
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
  intro t
  change t ∈ involutionCentralizer x ↔ e t ∈ involutionCentralizer y
  simp only [mem_centralizer_singleton_iff, ← he, ← map_mul, e.injective.eq_iff]

/-- The source pair count at the second representative is constant on its
ambient conjugacy class, including the change of class label. -/
theorem sourceCount_at_other_eq {D : Seed G} {t u : G}
    (ht : OtherInvolution D t) (hu : OtherInvolution D u) :
    sourceCount D.z t t = sourceCount D.z u u := by
  have htu : IsConj t u := ht.isConj hu
  calc
    sourceCount D.z t t = sourceCount D.z t u := by
      rw [sourceCount_eq_kappa D.localType.involution ht.1 ht.2 ht.1,
        sourceCount_eq_kappa D.localType.involution ht.1 ht.2 hu.1]
      exact TwoInvolutionClassOrder.kappa_eq_of_isConj D.z t htu
    _ = sourceCount D.z u u := by
      apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
      intro p
      constructor
      · rintro ⟨hp1, hp2, hpu⟩
        exact ⟨hp1, htu.symm.trans hp2, hpu⟩
      · rintro ⟨hp1, hp2, hpu⟩
        exact ⟨hp1, htu.trans hp2, hpu⟩

/-- Equality with the full centralizer follows from the actual inclusion and
order, even when the hypothesized order was given at a different representative. -/
theorem centralizer_eq_of_le_and_card48 {D : Seed G} {t u : G}
    (ht : OtherInvolution D t) (hu : OtherInvolution D u)
    (hC : Nat.card (involutionCentralizer t) = 48)
    (B : Subgroup G) (hB : B ≤ involutionCentralizer u) (hcard : Nat.card B = 48) :
    involutionCentralizer u = B := by
  have hCu : Nat.card (involutionCentralizer u) = 48 :=
    (centralizer_card_conj (ht.isConj hu)).symm.trans hC
  exact (eq_of_le_of_card_ge hB (by rw [hCu, hcard])).symm

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
