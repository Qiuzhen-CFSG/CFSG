module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic

/-!
# The A₅ specialization of the earlier module classification

The input below quantifies over every original faithful local component and
every member of the literal Irr⁺(K,R₂(KT),T) family. Its conclusion is an
actual equivariant alternating natural-module model. This is the A₅ case of
13.3.2(3), not the different four-dimensional natural SL₂(4) module.

The counterexample record implies all of Hypothesis 13.3.1 and also retains
the later exclusions used by the Chapter 14 consumer. The earlier universal
classification remains with `qt-13-03-preliminaries`; this file defines its
precise specialization and proves the elementary order consequence. It does
not assert that the universal classification has already been proved.

Source: Aschbacher–Smith, Lemma 13.3.2(3), printed p.885, and Theorem
12.2.2(3d), printed p.795 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource
open Chapter12.Section02
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u

/-- The exact natural A₅ alternative, universally on the original source family. -/
@[expose] def AlternatingFiveModules1332 : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L : Subgroup G),
    Counterexample T L → ∀ K ∈ MainForward.faithfulLocalComponents T,
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
      ∀ (U : Subgroup G), ChosenModule T K U →
        Chapter6.Source.IsConjugationModel K U Chapter6.Source.a5Module

/-- The source alternating natural module has sixteen elements. -/
theorem alternatingFive_model_card {G : Type u} [Group G] {K U : Subgroup G}
    (h : Chapter6.Source.IsConjugationModel K U Chapter6.Source.a5Module) :
    Nat.card U = 16 := by
  rw [h.card, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)]
  rfl

end CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource
