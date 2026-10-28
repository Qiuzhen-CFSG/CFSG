module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.Applicability
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.RankComparison
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The exhaustive B.5.6 side of the bad-character comparison

Start with the complete source conclusion, including every B.5.1 module
clause. Three-rank one eliminates the three product alternatives. In the
quasisimple case it eliminates all components except binary SL₂ and odd-degree
SL₃; the full B.5.1 extension clause leaves only S₅ as a proper extension.
A quasisimple SL₂ component cannot have field degree one, since SL₂(2) is S₃.

These are consequences of the full universal input, not a reduced
classification premise. If the ambient generalized Fitting subgroup is
quasisimple, the genuine offender-generation argument excludes S₃ as well.
The comparison with the thirteen F.6.18 rows remains separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1,
pp.99–103, B.5.6, pp.104–105, applied in the repair of 15.3.68, pp.1154–1155.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

private theorem symmetric_three_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))

omit [Finite D] in
private theorem quasisimple_not_solvable (h : IsQuasisimple D) : ¬ Group.IsSolvable D := by
  let : IsQuasisimple D := h
  let : IsSimpleGroup (D ⧸ center D) := h.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact Group.IsPerfect.not_isSolvable D

omit [Finite D] in
private theorem linearTwo_degree_ge_two (h : IsQuasisimple D)
    (F : BinaryField) (e : D ≃* SL(2,F.Carrier)) : 2 ≤ F.degree := by
  by_contra hn
  have hd : F.degree = 1 := by have := F.degree_pos; omega
  let : Fintype F.Carrier := Fintype.ofFinite _
  let a : F.Carrier ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, F.card_eq, hd]
    simp)
  let b := e.trans ((Atlas.fieldEquivSL 2 a).trans SLTwoPermThree.sl2Two_equiv_perm_three.some)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := symmetric_three_solvable
  exact quasisimple_not_solvable h (Group.isSolvable_of_isSolvable_injective (f := b.toMonoidHom) b.injective)

/-- Only S₅ survives the *full* proper-extension clause of B.5.1(1i). -/
theorem outerNatural_rank_one (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (h : OuterNaturalAction ρ) :
    Nonempty (D ≃* Equiv.Perm (Fin 5)) := by
  rcases h with h | h
  · obtain ⟨n, hlo, _, ⟨e⟩⟩ := h
    have hn : n = 5 := by
      by_contra hn
      have h6 : 6 ≤ n := by omega
      have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank h6
      have hu := (primeRank_le_of_injective 3 (alternatingGroup (Fin n)).subtype
        Subtype.val_injective).trans ((primeRank_equiv 3 e.groupEquiv).symm.le.trans hr)
      omega
    subst n
    exact ⟨e.groupEquiv⟩
  · obtain ⟨e⟩ := h
    have hl := (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
      (F := ZMod 2)).trans (primeRank_le_of_injective 3
        (commutator (Atlas.G2.Model (ZMod 2))).subtype Subtype.val_injective)
    have hu := (primeRank_equiv 3 e.groupEquiv).symm.le.trans hr
    omega

/-- This is a derived consequence of every B.5.1 clause, with actual actor
isomorphisms. The source action conclusion remains available to consumers. -/
theorem quasisimple_source_rank_one (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (hq : IsQuasisimple (generalizedFitting D))
    (c : QuasisimpleSourceConclusion ρ (generalizedFitting D)) :
    (∃ F : BinaryField, 2 ≤ F.degree ∧ Nonempty (D ≃* SL(2,F.Carrier))) ∨
      (∃ F : BinaryField, Odd F.degree ∧ Nonempty (D ≃* SL(3,F.Carrier))) ∨
      Nonempty (D ≃* Equiv.Perm (Fin 5)) := by
  have hwhole (hw : generalizedFitting D = ⊤) :
      (∃ F : BinaryField, 2 ≤ F.degree ∧ Nonempty (D ≃* SL(2,F.Carrier))) ∨
        (∃ F : BinaryField, Odd F.degree ∧ Nonempty (D ≃* SL(3,F.Carrier))) ∨
        Nonempty (D ≃* Equiv.Perm (Fin 5)) := by
    have hrL := (primeRank_le_of_injective 3 (generalizedFitting D).subtype
      Subtype.val_injective).trans hr
    let t : D ≃* generalizedFitting D :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hw).symm
    rcases quasisimple_model_rank_one hrL (c.fittingModel ρ) with
      ⟨F, ⟨e⟩⟩ | ⟨F, ho, ⟨e⟩⟩
    · exact Or.inl ⟨F, linearTwo_degree_ge_two hq F e, ⟨t.trans e⟩⟩
    · exact Or.inr (Or.inl ⟨F, ho, ⟨t.trans e⟩⟩)
  cases c.clause_one with
  | irreducible _ _ _ _ he =>
    rcases he with hw | ⟨_, ho⟩
    · exact hwhole hw
    · exact Or.inr (Or.inr (outerNatural_rank_one _ hr ho))
  | doubleThree _ hw _ _ _ => exact hwhole hw
  | naturalDual _ _ hw _ => exact hwhole hw
  | repeatedNatural _ _ _ _ _ hw _ => exact hwhole hw

/-- Exhaust the complete B.5.6 conclusion at a nontrivial rank-one actor.
The displayed small list is proved here, never used as a universal input. -/
theorem source_actor_rank_one [Nontrivial D] (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (h : SourceAlternative ρ) :
    Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨
      (∃ F : BinaryField, 2 ≤ F.degree ∧ Nonempty (D ≃* SL(2,F.Carrier))) ∨
      (∃ F : BinaryField, Odd F.degree ∧ Nonempty (D ≃* SL(3,F.Carrier))) ∨
      Nonempty (D ≃* Equiv.Perm (Fin 5)) := by
  rcases source_alternative_rank_one ρ hr h with hs | h
  · exact (not_subsingleton D hs).elim
  rcases h with ⟨hq, ⟨c⟩⟩ | h
  · exact Or.inr (quasisimple_source_rank_one ρ hr hq c)
  · obtain ⟨c⟩ := h
    exact Or.inl ⟨c.equiv⟩

/-- The component-containment argument eliminates the S₃ offender actor
without using any ordinary-Thompson identification or geometric shortcut. -/
theorem offender_source_rank_one (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥) (hL : IsQuasisimple (generalizedFitting D))
    (h : SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)) :
    (∃ F : BinaryField, 2 ≤ F.degree ∧ Nonempty ((offenderSubgroup ρ) ≃* SL(2,F.Carrier))) ∨
      (∃ F : BinaryField, Odd F.degree ∧ Nonempty ((offenderSubgroup ρ) ≃* SL(3,F.Carrier))) ∨
      Nonempty ((offenderSubgroup ρ) ≃* Equiv.Perm (Fin 5)) := by
  let : Nontrivial (offenderSubgroup ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  rcases source_actor_rank_one _ ((primeRank_le_of_injective 3
    (offenderSubgroup ρ).subtype Subtype.val_injective).trans hr) h with h | h
  · obtain ⟨e⟩ := h
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := symmetric_three_solvable
    exact (offender_not_solvable ρ hne hcore hL
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  · exact h

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
