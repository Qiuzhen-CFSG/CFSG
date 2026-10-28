module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.Remaining
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.Dihedral
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.ModelBounds
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.ExceptionalOrders
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.ProductRow

/-!
# Complete nonsolvable F.6 comparison

The original small subnormal witness embeds faithfully in the bang
quotient. Component comparison excludes the classical alternatives and
identifies row (6) using that same witness. Row (1) contradicts the
supplied Sylow order obstruction, and row (2) remains explicit.

The product row is excluded by its specified outer actions, and the
alternating-cover, symmetric and Mathieu rows by their actual component
orders. Thus all thirteen rows, in either orientation of the actual bang
images, give RowTwoModel or BangRecognition. No recognition is inferred
from group order alone. The application to Preparation.classified_bang
retains its full universal F.6.18 premise explicitly; the parent owns its
discharge and the separate exclusion of row (2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.7.70, printed pp.1074–1075 (PDF pp.1091–1092), and F.6.18,
printed pp.309–310.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
open Representation Chapter12.Section08
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open FSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (c : CriticalPath (L := L) F)

/-- The actual bang component excludes the prime-linear, field-extension and
all four graph-component models. No rank-at-three premise is used. -/
theorem classical_bang_obstructions (small : SmallSubnormal c)
    (hq : IsQuasisimple (generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c)))) :
    (∀ f : FieldParameter.{u}, f.degree = 1 →
      (f.prime % 24 = 11 ∨ f.prime % 24 = 13) →
      ¬ Nonempty (generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c)) ≃* PSL(2,f.Carrier))) ∧
    ¬ Nonempty (FieldExtensionRow (D := ((I c) ⧸ pPrimeCore 3 (I c)))) ∧
    ∀ p : ℕ, p.Prime → (p % 8 = 3 ∨ p % 8 = 5) →
      ¬ DegreeThree p (generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c))) := by
  obtain ⟨K, _, _, hN, hmN⟩ := retained_small_image c small
  refine ⟨?_, ?_, ?_⟩
  · intro f hd hc he
    obtain ⟨e⟩ := he
    exact not_prime_linear_component (K.map (plusToBang c)) hN hmN hq f hd hc e
  · rintro ⟨r⟩
    exact not_field_extension (K.map (plusToBang c)) hN hmN hq r
  · intro p hp hc h
    exact not_degreeThree_component (K.map (plusToBang c)) hN hmN hq hp hc h

/-- Row (6), including both of its model alternatives, supplies both
recognition outputs from the retained original subgroup. -/
theorem recognition_of_dihedral_row (small : SmallSubnormal c)
    (hq : IsQuasisimple (generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c))))
    (ht : generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c)) = ⊤)
    (S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c))) (hS : Nonempty (S ≃* DihedralGroup 4)) :
    Nonempty (BangRecognition c) := by
  obtain ⟨e⟩ := hS
  apply recognition_of_fitting_top c small hq ht S
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  decide

/-- Row (10)'s supplied Sylow model has order 32, so it is impossible. -/
theorem not_degreeThree_whole_row (small : SmallSubnormal c)
    (hq : IsQuasisimple (generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c))))
    (ht : generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c)) = ⊤)
    (S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c))) (hS : Nonempty (S ≃* W32)) : False := by
  obtain ⟨e⟩ := hS
  apply not_sylow_thirtyTwo_of_fitting_top c small hq ht S
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card]
  norm_num [C]

/-- Exhaust the full thirteen-row interface, retaining row (2) and the two
precise unfinished families. This is a reduction, not final recognition. -/
theorem comparison_or_unresolved (small : SmallSubnormal c)
    {A B : Subgroup ((I c) ⧸ pPrimeCore 3 (I c))}
    (S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c))) (hne : Nat.card S ≠ 2)
    (ha : Alternative A B S) :
    (RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) ∨ Nonempty (BangRecognition c)) ∨
      UnresolvedRow S := by
  obtain ⟨K, _, _, hN, hmN⟩ := retained_small_image c small
  cases ha with
  | one hs _ _ _ =>
    obtain ⟨e⟩ := hs
    exact (hne (by rw [Nat.card_congr e.toEquiv]; simp [C])).elim
  | two hm => exact Or.inl (Or.inl hm)
  | three r hs _ _ =>
    obtain ⟨e⟩ := hs
    exact Or.inr (Or.inl ⟨⟨r⟩, by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]⟩)
  | four f hd hc e ht hq _ _ _ =>
    have a : generalizedFitting ((I c) ⧸ pPrimeCore 3 (I c)) ≃*
        ((I c) ⧸ pPrimeCore 3 (I c)) := (MulEquiv.subgroupCongr ht).trans topEquiv
    exact (not_prime_linear_component (K.map (plusToBang c)) hN hmN hq f hd hc
      (a.trans e)).elim
  | five f hd hc _ e hq _ _ _ =>
    exact (not_prime_linear_component (K.map (plusToBang c)) hN hmN hq f hd hc e).elim
  | six _ ht hq hs _ _ =>
    exact Or.inl (Or.inr (recognition_of_dihedral_row c small hq ht S hs))
  | seven hm hq _ _ _ =>
    refine Or.inr (Or.inr ⟨hq, ?_⟩)
    rcases hm with hm | hm
    · exact Or.inl hm
    · exact Or.inr (Or.inl hm)
  | eight hm hq _ _ _ =>
    rcases hm with hm | hr
    · exact Or.inr (Or.inr ⟨hq, Or.inr (Or.inr (Or.inl hm))⟩)
    · obtain ⟨r⟩ := hr
      exact (not_field_extension (K.map (plusToBang c)) hN hmN hq r).elim
  | nine hm hq _ _ _ =>
    refine Or.inr (Or.inr ⟨hq, ?_⟩)
    rcases hm with hm | hm
    · exact Or.inr (Or.inr (Or.inr (Or.inl hm)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
  | ten _ _ _ _ ht hq hs _ _ =>
    exact (not_degreeThree_whole_row c small hq ht S hs).elim
  | eleven r hq _ _ _ =>
    exact (not_degreeThree_component (K.map (plusToBang c)) hN hmN hq
      r.prime_isPrime r.congruence r.model.model).elim
  | twelve e hq _ _ _ =>
    exact Or.inr (Or.inr ⟨hq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩))))⟩)
  | thirteen _ e hq _ _ _ =>
    exact (not_mathieu_component (K.map (plusToBang c)) hN hmN hq e).elim

/-- The actual two orientations supplied by Preparation use the same reduction. -/
theorem bang_comparison_or_unresolved (small : SmallSubnormal c)
    (S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c))) (hne : Nat.card S ≠ 2)
    (ha : Alternative (bang c (group F L)) (bang c (YT c)) S ∨
      Alternative (bang c (YT c)) (bang c (group F L)) S) :
    (RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) ∨ Nonempty (BangRecognition c)) ∨
      UnresolvedRow S := by
  rcases ha with ha | ha <;> exact comparison_or_unresolved c small S hne ha

/-- The complete thirteen-row comparison, retaining exactly row (2) or
the two actual equivalences required by BangRecognition. -/
theorem comparison (small : SmallSubnormal c)
    {A B : Subgroup ((I c) ⧸ pPrimeCore 3 (I c))}
    (S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c))) (hne : Nat.card S ≠ 2)
    (ha : Alternative A B S) :
    RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) ∨ Nonempty (BangRecognition c) := by
  rcases comparison_or_unresolved c small S hne ha with h | h
  · exact h
  · rcases h with ⟨⟨r⟩, hS⟩ | ⟨hq, hm⟩
    · exact (not_bang_product_row c small S hS r).elim
    · exact (exceptional_bang_obstruction c small hq hm).elim

/-- Apply the comparison to either orientation of the original bang images.
The literal common-Sylow equality is retained from the classification input;
the row comparison itself already works for arbitrary local subgroups. -/
theorem bang_comparison (small : SmallSubnormal c)
    (S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c)))
    (_hS : bang c (group F L) ⊓ bang c (YT c) = (S : Subgroup _))
    (hne : Nat.card S ≠ 2)
    (ha : Alternative (bang c (group F L)) (bang c (YT c)) S ∨
      Alternative (bang c (YT c)) (bang c (group F L)) S) :
    RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) ∨ Nonempty (BangRecognition c) := by
  rcases ha with ha | ha <;> exact comparison c small S hne ha

/-- The source-data consumer: Preparation supplies the actual common Sylow,
its order obstruction, and all F.6.18 rows. Only the independent row-(2)
exclusion remains for the parent to obtain unconditional BangRecognition. -/
theorem classified_bang_comparison (d : Data T L V F W)
    (sourceF : ClassificationInput KnownSimple.IsKnownSimple.{u})
    (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c) :
    RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) ∨ Nonempty (BangRecognition c) := by
  obtain ⟨S, hS, hne, ha⟩ := classified_bang d c sourceF h k small
  exact bang_comparison c small S hS hne ha

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
