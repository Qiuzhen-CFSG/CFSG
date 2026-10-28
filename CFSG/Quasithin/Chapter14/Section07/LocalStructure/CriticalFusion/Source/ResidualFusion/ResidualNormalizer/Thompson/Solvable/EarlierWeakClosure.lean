module

public import CFSG.Quasithin.Chapter12.Section08.Setup.SourceData
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure
public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# The universal earlier weak-closure input

This is the complete implication of 14.7.31 on the original counterexample,
with the natural L₃(2) setup, abelian U, and the plane-centralizer hypothesis. Both conclusions
use the literal corank-zero weak closure. The second clause retains the
relative Sylow, reduced module, actual symmetric-three quotient and the
returning-point condition. It does not assert the theorem as an axiom.

The producer is qt-14-07-components; the 14.7.67 assembly must supply this
earlier theorem. In particular this interface supplies no S₃ recognition
or core identity for the later group J(DR₁)R₁.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.7.31, printed p.1055, PDF p.1072.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u

/-- The two full clauses of the earlier source implication, universally over
the original higher-rank setup. It remains a theorem parameter. -/
def Theorem14731 : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Counterexample T L →
    HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3 →
    ∀ F : InvariantFlag T V 3, IsMulCommutative F.U →
      centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) →
      (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 ≤ L ⊔ (T : Subgroup G) ∧
        L ⊔ (T : Subgroup G) ≤
          normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) ∧
        normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) ≤
          normalizer (L : Set G)) ∧
      ∀ A R B : Subgroup G, HasCharacteristicTwo A →
        Chapter1.IsSylowIn 2 R A → B ≤ A → IsPReduced 2 (B.subgroupOf A) →
        Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) →
        A ⊓ centralizer (B : Set G) = A.pCoreIn 2 →
        (∀ g : G, conjugate (F.Vi 1) g ≤ B →
          conjugate F.U g ≤ A ⊓ centralizer (B : Set G)) →
        ChapterE.indexedWeakClosure V R 0 ≤ A ∧
          A ≤ normalizer (ChapterE.indexedWeakClosure V R 0 : Set G)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
