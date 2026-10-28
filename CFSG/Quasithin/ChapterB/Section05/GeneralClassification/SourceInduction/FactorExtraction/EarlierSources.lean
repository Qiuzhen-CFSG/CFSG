module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModuleContract

/-!
# Earlier source implications used by factor extraction

These are the universal earlier implications, with their genuine hypotheses,
needed in B.5.8 and B.5.11. B.4.8(3) applies only after dimension four,
indecomposability, faithfulness and an actual natural moved module have been
proved. A.1.31(1) assumes the rank bound on the covering group, retaining the
normal quotient and its characteristic-p generalized Fitting subgroup.

The definitions do not prove either source theorem. Their existing producers
are `qt-b-04-natural-extensions` and `qt-a-01-section-rank`, respectively; the
source-classification assembly owner must instantiate these implications.
Neither input assumes rank-one extraction, a reduced classifier or a
four-dimensional extension of the current arbitrary module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.1.31(1),
printed pp.27–28, and B.4.8(3), printed p.91.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
open QuasisimpleSource
universe u v

/-- The full behavioral conclusion of B.4.8(3), under its source hypotheses.
The chosen natural identification controls the actual full-axis offender family. -/
def EarlierB48Three : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (U : Type v) [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
    (σ : Representation (ZMod 2) D U),
    Function.Injective σ → IsIndecomposable σ → Module.finrank (ZMod 2) U = 4 →
    ∀ (W : Subrepresentation σ), W.toSubmodule = moved σ ⊤ →
    ∀ e : ActionEquiv W.toRepresentation (linearNatural BinaryField.two 3),
      (∀ A, IsBestOffender σ A ↔
        IsFullAxisGroup BinaryField.two 3 (A.map e.groupEquiv.toMonoidHom)) ∧
      quadraticRatio σ = 1 ∧
      (∀ a : D, orderOf a = 2 →
        moved σ (zpowers a) = fixedSpace σ (zpowers a) ∧
        Module.finrank (ZMod 2) (fixedSpace σ (zpowers a)) = 2 ∧
        fixedSpace σ (zpowers a) ≤ W.toSubmodule)

/-- A.1.31(1), retaining the covering rank and the literal normal quotient.
The intersection represents the relative centralizer inside its p-core. -/
def EarlierA131One : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime → Odd p →
    primeRank p G ≤ 2 → ∀ (N : Subgroup G) [N.Normal],
      generalizedFitting (G ⧸ N) = pCore p (G ⧸ N) →
      ∀ T : Subgroup (G ⧸ N), IsPGroup 2 T → T ≠ ⊥ →
        IsCyclic ↥(pCore p (G ⧸ N) ⊓ centralizer (T : Set (G ⧸ N)))

end CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
