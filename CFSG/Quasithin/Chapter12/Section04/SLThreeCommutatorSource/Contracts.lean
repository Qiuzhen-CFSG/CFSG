module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.Setup
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# Independent earlier inputs to the L₃ commutator construction

These are source obligations, not asserted theorems. The first identifies
the action of the full normalizer with the original L-action. The second
is the hyperplane-centralizer assertion proved by 12.4.8. The third is
the L₃ instance of the coset-geometry argument in 12.4.1. The assembly
uses them to construct and symmetrize the actual commutator plane.

The source producers must discharge these implications from their
displayed hypotheses. In particular the bound does not assume fixed-space
vanishing, and conjugate existence does not assume a commutator plane.

Source: Aschbacher–Smith, 12.2.8 and 12.4.1, 12.4.8–9, pp.797,812,815–816.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
open Section02 SmallFusion ChapterE
universe u

/-- The original full normalizer induces the same action as L. -/
def NormalizerAction : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    ∀ n ∈ normalizer (V : Set X), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v

/-- The precise centralizer bound needed from 12.4.8, on every actual
hyperplane of the original V. The numerical r-bound is deduced from it. -/
def HyperplaneCentralizers1248 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    ∀ U ≤ V, subgroupCorank V U = 1 →
      centralizer (U : Set X) ≤ normalizer (V : Set X)

/-- The L₃ source application of 12.4.1, retaining both of its additional
hypotheses and the literal mutual-normalization commutator conclusion. -/
def NoncommutingConjugate1241 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    centralizer (omegaOneAmbient ((center (T : Subgroup X)).map
      (T : Subgroup X).subtype) : Set X) ≤ normalizer (L : Set X) →
    letI := D.elementary
    1 < globalS V → ∃ g : X,
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
        V ⊓ V.map (MulAut.conj g).toMonoidHom

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
