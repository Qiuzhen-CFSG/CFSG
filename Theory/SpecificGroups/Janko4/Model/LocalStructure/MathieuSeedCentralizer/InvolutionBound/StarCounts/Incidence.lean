module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarDefs
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Level1
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# Conjugacy-class incidences with ordered star pairs

Count the same incidences by conjugates and by ordered distinct pairs.
Conjugation identifies the invariant-pair fibers; the first two certified
star stabilizer transversals prove transitivity on all 552 pairs. Each
unordered invariant pair occurs with both orderings, giving 24 and 72 for
the two literal representatives. This counts the actual `StarClass` carrier.

Source: the concrete star tables and representatives in `StarDefs`, and the
word certificates in `Image.StarOrder.Level0` and `Level1`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
open Janko4.Cardinality.QuotientCount.Image
open Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate

private theorem conj_iff {G : Type*} [Group G] (g a u : G) :
    IsConj a (MulAut.conj g u) ↔ IsConj a u := by
  have h : IsConj u (MulAut.conj g u) := isConj_iff.mpr ⟨g, rfl⟩
  exact ⟨fun h' => h'.trans h.symm, fun h' => h'.trans h⟩

private theorem incidence_balance {G X : Type*} [Group G] [Finite G] [Finite X]
    (a : G) (x : X) (act : G → X ≃ X) (R : G → X → Prop)
    (heq : ∀ g u y, R (MulAut.conj g u) (act g y) ↔ R u y)
    (htrans : ∀ y, ∃ g, act g x = y) :
    Nat.card X * Nat.card {u : G // IsConj a u ∧ R u x} =
      Nat.card {u : G // IsConj a u} * Nat.card {y : X // R a y} := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let : Fintype {u : G // IsConj a u} := Fintype.ofFinite _
  let e : (Σ y : X, {u : G // IsConj a u ∧ R u y}) ≃
      (Σ u : {u : G // IsConj a u}, {y : X // R u.val y}) :=
    { toFun p := ⟨⟨p.2.val, p.2.property.1⟩, ⟨p.1, p.2.property.2⟩⟩
      invFun p := ⟨p.2.val, ⟨p.1.val, p.1.property, p.2.property⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hleft (y : X) : Nat.card {u : G // IsConj a u ∧ R u y} =
      Nat.card {u : G // IsConj a u ∧ R u x} := by
    obtain ⟨g, rfl⟩ := htrans y
    apply Eq.symm
    apply Nat.card_congr
    apply Equiv.subtypeEquiv (MulAut.conj g).toEquiv
    intro u
    change (IsConj a u ∧ R u x) ↔ (IsConj a (MulAut.conj g u) ∧ R (MulAut.conj g u) (act g x))
    rw [conj_iff, heq]
  have hright (u : {u : G // IsConj a u}) : Nat.card {y : X // R u.val y} =
      Nat.card {y : X // R a y} := by
    obtain ⟨g, hg⟩ := isConj_iff.mp u.property
    rw [← hg]
    apply Eq.symm
    exact Nat.card_congr (Equiv.subtypeEquiv (act g) (fun y => (heq g a y).symm))
  have h := Nat.card_congr e
  simp only [Nat.card_sigma, hleft, hright, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Nat.card_eq_fintype_card] at h
  exact h

private abbrev OrderedPair := {p : Fin 24 × Fin 24 // p.1 ≠ p.2}

private def movePair (g : StarGroup) : OrderedPair ≃ OrderedPair where
  toFun p := ⟨(g.val p.val.1, g.val p.val.2), g.val.injective.ne p.property⟩
  invFun p := ⟨(g.val.symm p.val.1, g.val.symm p.val.2), g.val.symm.injective.ne p.property⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

private def preservesPair (g : StarGroup) (p : OrderedPair) : Prop :=
  (g.val p.val.1 = p.val.1 ∧ g.val p.val.2 = p.val.2) ∨
  (g.val p.val.1 = p.val.2 ∧ g.val p.val.2 = p.val.1)

private instance (g : StarGroup) (p : OrderedPair) : Decidable (preservesPair g p) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

private theorem preservesPair_conj (g u : StarGroup) (p : OrderedPair) :
    preservesPair (MulAut.conj g u) (movePair g p) ↔ preservesPair u p := by
  change ((g.val * u.val * g.val⁻¹) (g.val p.val.1) = g.val p.val.1 ∧
      (g.val * u.val * g.val⁻¹) (g.val p.val.2) = g.val p.val.2) ∨
    ((g.val * u.val * g.val⁻¹) (g.val p.val.1) = g.val p.val.2 ∧
      (g.val * u.val * g.val⁻¹) (g.val p.val.2) = g.val p.val.1) ↔ _
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq]
  rfl

private theorem rep1_surjective (j : Fin 24) (hj : j ≠ 0) :
    ∃ k, rep1 k 1 = j := by
  let f : Fin 23 → {v : Fin 24 // v ≠ 0} := fun k => ⟨rep1 k 1, by
    have hf : rep1 k 0 = 0 := level1_fix ⟨rep1 k, word_mem _ _ (gen_mem _) _⟩
    intro he
    have hh := (rep1 k).injective (he.trans hf.symm)
    exact (by decide : (1 : Fin 24) ≠ 0) hh⟩
  have hi : Function.Injective f := fun _ _ h => rep1_inj (congrArg Subtype.val h)
  have hc : Nat.card {v : Fin 24 // v ≠ 0} ≤ Nat.card (Fin 23) := by
    rw [Nat.card_eq_fintype_card, Nat.card_fin]
    decide +kernel
  obtain ⟨k, hk⟩ := hi.bijective_of_nat_card_le hc |>.surjective ⟨j, hj⟩
  exact ⟨k, congrArg Subtype.val hk⟩

private def markedPair : OrderedPair := ⟨(0, 1), by decide⟩

private theorem movePair_transitive (p : OrderedPair) :
    ∃ g : StarGroup, movePair g markedPair = p := by
  obtain ⟨i, hi⟩ := rep0_inj.bijective_of_finite.surjective p.val.1
  have hne : (rep0 i)⁻¹ p.val.2 ≠ 0 := by
    intro h
    have hh := congrArg (rep0 i) h
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hh
    exact p.property (hi.symm.trans hh.symm)
  obtain ⟨j, hj⟩ := rep1_surjective ((rep0 i)⁻¹ p.val.2) hne
  have hm0 : rep0 i ∈ StarGroup := level0_le (word_mem _ _ (gen_mem _) _)
  have hm1 : rep1 j ∈ StarGroup := level0_le (level1_le (word_mem _ _ (gen_mem _) _))
  refine ⟨⟨rep0 i * rep1 j, StarGroup.mul_mem hm0 hm1⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change rep0 i (rep1 j 0) = p.val.1
    rw [level1_fix ⟨rep1 j, word_mem _ _ (gen_mem _) _⟩]
    exact hi
  · change rep0 i (rep1 j 1) = p.val.2
    rw [hj, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

private theorem orderedPair_card : Nat.card OrderedPair = 552 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 10000 in
private theorem preservesPair_false_card :
    Nat.card {p : OrderedPair // preservesPair (starBase false) p} = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 10000 in
private theorem preservesPair_true_card :
    Nat.card {p : OrderedPair // preservesPair (starBase true) p} = 72 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem marked_card (b : Bool) :
    Nat.card {g : StarGroup // IsConj (starBase b) g ∧ preservesPair g markedPair} =
      Nat.card (StarClass b) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl _)
  intro g
  change (IsConj (starBase b) g ∧ _) ↔ (_ ∧ IsConj (starBase b) g)
  rw [pairLabel_eq_one_iff]
  exact and_comm

/-- Double counting on the actual star conjugacy class and ordered pairs. -/
theorem starClass_incidence (b : Bool) :
    552 * Nat.card (StarClass b) =
      Nat.card {g : StarGroup // IsConj (starBase b) g} *
        (if b then 72 else 24) := by
  have h := incidence_balance (starBase b) markedPair movePair preservesPair
    preservesPair_conj movePair_transitive
  rw [orderedPair_card, marked_card] at h
  cases b
  · simpa only [preservesPair_false_card, Bool.false_eq_true, ↓reduceIte] using h
  · simpa only [preservesPair_true_card, ↓reduceIte] using h

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
