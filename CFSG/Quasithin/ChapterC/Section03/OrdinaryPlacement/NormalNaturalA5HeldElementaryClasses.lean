module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.FiniteFusion
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.FiniteStructure
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB

/-!
# Exact involution-class labels on the native Held Sylow words

The existing checked fusion forest gives actual conjugators. Retaining its
root label distinguishes the two classes, whose centralizers have different
proved orders. Thus the finite Boolean label below equals genuine conjugacy
to the original ATLAS generator a.

Source: GLS3 Table 5.3p and Aschbacher--Smith 12.7.5, printed p.840.
-/

@[expose] public section
open Subgroup
namespace Held.OrdinaryElementary
open InvolutionFixedData InvolutionFixedData.Coverage
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

private theorem centralizer_card_conj {x y : He} (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set He)) = Nat.card (centralizer ({y} : Set He)) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  let f := MulAut.conj g
  have he : f x = y := hg
  rw [←he]
  apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
  intro a
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro ha
    change f a * f x = f x * f a
    simpa only [map_mul] using congrArg f ha
  · intro ha
    change f a * f x = f x * f a at ha
    apply f.injective
    simpa only [map_mul] using ha

private theorem representatives_not_conjugate :
    ¬ IsConj a (TwoLocalCandidates.max5First ^ 4) := by
  intro h
  have hc := centralizer_card_conj h
  have ha : Nat.card (centralizer ({a} : Set He)) = 161280 :=
    by simpa only [TwoA.centralizer,MulAut.fixedSubgroup_conj] using
      TwoA.FiniteStructure.centralizer_card
  have hb : Nat.card (centralizer ({TwoLocalCandidates.max5First ^ 4} : Set He)) = 21504 := by
    rw [←MulAut.fixedSubgroup_conj]
    exact twoB_fixedSubgroup_card
  omega

private theorem forest_root_constant (i : Fin 191)
    (hi : (forestParent i).val < i.val) : forestRoot (forestParent i) = forestRoot i := by
  have h : ∀ i : Fin 191, (forestParent i).val < i.val →
      forestRoot (forestParent i) = forestRoot i := by decide +kernel
  exact h i hi

/-- Every forest element is conjugate to its exact labelled representative. -/
theorem forest_isConj_root (i : Fin 191) :
    IsConj (rootRepresentative (forestRoot i)) (normalForm (forestIndex i)).val := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    rcases forest_parent_lt_or_root i with hp | hr
    · have hprev := ih (forestParent i) hp
      rw [forest_root_constant i hp] at hprev
      exact hprev.trans (isConj_iff.mpr ⟨_,forest_edge_identity i hp⟩)
    · rw [hr]
      exact isConj_iff.mpr ⟨_,root_conjugation_identity (forestRoot i)⟩

/-- The checked forest's zero root label is exactly the actual Held 2A class. -/
theorem forest_isConj_a_iff (i : Fin 191) :
    IsConj a (normalForm (forestIndex i)).val ↔ rootClass (forestRoot i) = 0 := by
  have hc := forest_isConj_root i
  unfold rootRepresentative at hc
  split at hc
  next h => exact ⟨fun _ => h,fun _ => hc⟩
  next h => exact ⟨fun ha => (representatives_not_conjugate (ha.trans hc.symm)).elim,
    fun hh => (h hh).elim⟩

/-- Computable exact class label on all 1024 literal Sylow words. -/
def classA (n : Fin 1024) : Bool :=
  (n != 0) && decide (forestIndex (forestRow n) = n) &&
    decide (rootClass (forestRoot (forestRow n)) = 0)

/-- The finite label is equivalent to conjugacy in Held, with no classification premise. -/
theorem classA_iff (n : Fin 1024) :
    classA n = true ↔ IsConj a (normalForm n).val := by
  constructor
  · intro h
    have ⟨⟨_,hi⟩,hc⟩ : ((n != 0) = true ∧ decide (forestIndex (forestRow n) = n) = true) ∧
        decide (rootClass (forestRoot (forestRow n)) = 0) = true := by
      simpa only [classA,Bool.and_eq_true] using h
    have hi : forestIndex (forestRow n) = n := of_decide_eq_true hi
    have hc : rootClass (forestRoot (forestRow n)) = 0 := of_decide_eq_true hc
    rw [←hi]
    exact (forest_isConj_a_iff _).mpr hc
  · intro h
    have ho : orderOf (normalForm n).val = 2 := by
      obtain ⟨g,hg⟩ := isConj_iff.mp h
      rw [←hg]
      exact ((MulAut.conj g).orderOf_eq a).trans orderOf_a
    obtain ⟨i,hi⟩ := normalForm_involution_index n ho
    have hn : n ≠ 0 := by
      intro he
      rw [he,normalForm_zero,orderOf_one] at ho
      omega
    have hrow : forestIndex (forestRow n) = n := by
      have hh : ∀ i : Fin 191, forestIndex (forestRow (forestIndex i)) = forestIndex i := by
        decide +kernel
      rw [←hi]
      exact hh i
    have hc : rootClass (forestRoot (forestRow n)) = 0 :=
      (forest_isConj_a_iff _).mp (by simpa only [hrow] using h)
    simp only [classA,Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq]
    exact ⟨⟨hn,hrow⟩,hc⟩

end Held.OrdinaryElementary
