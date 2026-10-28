module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Generation
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HyperplaneFaithfulness
/-!
# All B.5.3 hypotheses at the two recursive factors

The actual internal product gives normality, strict cardinal descent and the
trivial two-core of the second factor. Its faithful action on the second
subspace follows either from the whole-space supplement or from the invariant
hyperplane argument. B.1.5 supplies offender generation, and the inverse-image
construction supplies the finite SQTK cover.

`FFHypothesis.classify_second` applies a strictly smaller-order induction
hypothesis only to this factor and this restricted action. It neither assumes
nor proves the classification at the current order. The existence of the
product and its source module identifications remains part of B.5.8–B.5.10.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.8 and B.5.11,
printed pp.106 and 109. The nontrivial offender existence uses the literal
definition of J(G,V), and its minimal version uses proved B.1.4.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
universe u v
variable {D : Type u} [Group D] [Finite D]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) D V) {K : GroupClass.{u}}

/-- Nontrivial offender-generated actors have an actual best offender. -/
theorem FFHypothesis.exists_bestOffender [Nontrivial D] (hyp : FFHypothesis K ρ) :
    ∃ A, IsBestOffender ρ A := by
  by_contra! hn
  have hbot : offenderSubgroup ρ ≤ ⊥ := by
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩
    exact (hn A hA).elim
  rw [hyp.generated] at hbot
  exact top_ne_bot (le_antisymm hbot bot_le)

/-- The minimal offender selected after B.5.8 exists. -/
theorem FFHypothesis.exists_minimalBestOffender [Nontrivial D] (hyp : FFHypothesis K ρ) :
    ∃ A, IsMinimalBestOffender ρ A := by
  obtain ⟨A,hA⟩ := hyp.exists_bestOffender ρ
  obtain ⟨B,hB,_⟩ := hA.exists_minimal ρ
  exact ⟨B,hB⟩

/-- Nontriviality in B.5.3 supplies the FF witness needed by consumers. -/
theorem FFHypothesis.isFFModule [Nontrivial D] (hyp : FFHypothesis K ρ) : IsFFModule ρ := by
  let : Module.Finite (ZMod 2) V := hyp.finite_module
  obtain ⟨A,hA⟩ := hyp.exists_bestOffender ρ
  exact ⟨A,hA.isOffender ρ⟩

/-- Every B.5.3 hypothesis holds on the original complementary factor. -/
theorem FFHypothesis.on_second (hyp : FFHypothesis K ρ)
    {A B : Subgroup D} (h : InternalProduct A B)
    (U W : Subrepresentation ρ)
    (hU : U.toSubmodule ≤ fixedSpace ρ B)
    (hW : W.toSubmodule ≤ fixedSpace ρ A)
    (hs : U.toSubmodule ⊔ W.toSubmodule = ⊤ ∨
      Module.finrank (ZMod 2) (V ⧸ (U.toSubmodule ⊔ W.toSubmodule)) = 1) :
    FFHypothesis K (W.toRepresentation.comp B.subtype) := by
  let : Module.Finite (ZMod 2) V := hyp.finite_module
  have hf : Function.Injective (W.toRepresentation.comp B.subtype) := by
    rcases hs with hs | hd
    · exact faithful_on_supplement ρ hyp.faithful B U W hs hU
    · exact faithful_on_hyperplane_supplement ρ hyp.faithful hyp.twoCore B U W hd hU
  refine ⟨inferInstance, hf, h.second_twoCore hyp.twoCore,
    second_generated ρ h W hW hf hyp.generated, ?_⟩
  obtain ⟨q⟩ := hyp.quotient
  exact ⟨q.subgroup B⟩

/-- The genuine order decrease and all source hypotheses, in one application. -/
theorem FFHypothesis.descent_to_second (hyp : FFHypothesis K ρ)
    {A B : Subgroup D} (h : InternalProduct A B) (hA : A ≠ ⊥)
    (U W : Subrepresentation ρ)
    (hU : U.toSubmodule ≤ fixedSpace ρ B)
    (hW : W.toSubmodule ≤ fixedSpace ρ A)
    (hs : U.toSubmodule ⊔ W.toSubmodule = ⊤ ∨
      Module.finrank (ZMod 2) (V ⧸ (U.toSubmodule ⊔ W.toSubmodule)) = 1) :
    Nat.card B < Nat.card D ∧ FFHypothesis K (W.toRepresentation.comp B.subtype) :=
  ⟨h.second_card_lt hA, hyp.on_second ρ h U W hU hW hs⟩

/-- Only the strictly smaller orders of a strong-induction hypothesis.
This is not an earlier-source premise and must be bound by the final induction. -/
def SmallerClassification (K : GroupClass.{u}) (n : ℕ) : Prop :=
  ∀ (E : Type u) [Group E] [Finite E], Nat.card E < n →
    ∀ (X : Type v) [AddCommGroup X] [Module (ZMod 2) X]
      (σ : Representation (ZMod 2) E X), FFHypothesis K σ → AdequateAlternative σ

/-- Apply recursion to the actual second subgroup after proving strict descent. -/
theorem FFHypothesis.classify_second (hyp : FFHypothesis K ρ)
    (ih : SmallerClassification.{u,v} K (Nat.card D))
    {A B : Subgroup D} (h : InternalProduct A B) (hA : A ≠ ⊥)
    (U W : Subrepresentation ρ)
    (hU : U.toSubmodule ≤ fixedSpace ρ B)
    (hW : W.toSubmodule ≤ fixedSpace ρ A)
    (hs : U.toSubmodule ⊔ W.toSubmodule = ⊤ ∨
      Module.finrank (ZMod 2) (V ⧸ (U.toSubmodule ⊔ W.toSubmodule)) = 1) :
    AdequateAlternative (W.toRepresentation.comp B.subtype) := by
  obtain ⟨hlt,hypB⟩ := hyp.descent_to_second ρ h hA U W hU hW hs
  exact ih B hlt W.toSubmodule (W.toRepresentation.comp B.subtype) hypB

omit [Finite D] in
/-- The source hyperplane is literally an index-two additive quotient. -/
theorem HyperplaneCase.quotient_card [Module.Finite (ZMod 2) V]
    (h : HyperplaneCase ρ) : Nat.card (V ⧸ (moved ρ ⊤ ⊔ ρ.invariants)) = 2 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), h.hyperplane]
  simp

end CFSG.Quasithin.ChapterB.SourceInduction
