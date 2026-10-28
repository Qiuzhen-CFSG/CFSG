module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.Basic
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.SmallSupport
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MovedFactors

/-!
# Fitting structure for binary offenders

This module owns the assembly of Aschbacher–Smith B.1.9–10, printed
pp.71–72 (PDF pp.82–83). The definitions retain the actual offender families,
relative odd cores, and canonical inclusions in all product and sum maps.

The local fixed-space restriction constructs faithful binary planes for every
noncentral minimal offender. The checked D.2.12 application and global splitting
then construct the internal products and support sum. Centrality of F in F(G)
and the bound [J*,A] ≤ F give clause (5). This supplies the universal B.1.9
input to the two quotient inductions proving B.1.10, including their literal
fixed-space kernels and the case F = 1. No local-plane, decomposition, or
earlier-source premise remains in the source theorems exported below.

The factors have actual S₃ isomorphisms; `Decomposition.projectiveFactorModel`
identifies them with the source L₂(2). All product and sum maps preserve the
original inclusions. The B.5 consumer adapter is in the separate extension
`FittingStructure.GeneralClassification`.
-/

public section

namespace CFSG.Quasithin.ChapterB.FittingStructure
open Subgroup Representation.BinaryOffender Theory.GroupTheory
universe u v
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The final commutator argument in B.1.9(5). Its two structural premises
are outputs to be proved in the global splitting construction. -/
theorem minimal_moved_centralizes_of_control
    (hF : fittingMoved ρ ≤ centralizer (fittingSubgroup G : Set G))
    (hcomm : ∀ A, IsMinimalBestOffender ρ A → ⁅fittingSubgroup G, A⁆ ≠ ⊥ →
      ⁅minimalGenerated ρ, A⁆ ≤ fittingMoved ρ)
    {A K : Subgroup G} (hA : IsMinimalBestOffender ρ A) (hK : K = ⁅K, A⁆) :
    K ≤ minimalGenerated ρ ⊓ centralizer (fittingSubgroup G : Set G) := by
  have hKJ := moved_by_minimal_le ρ hA hK
  by_cases hc : A ≤ centralizer (fittingSubgroup G : Set G)
  · exact minimal_centralizing_case ρ hA hc hK
  · have hn : ⁅fittingSubgroup G, A⁆ ≠ ⊥ := by
      intro hz
      exact hc (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
    refine le_inf hKJ ?_
    calc
      K = ⁅K, A⁆ := hK
      _ ≤ ⁅minimalGenerated ρ, A⁆ := commutator_mono hKJ le_rfl
      _ ≤ fittingMoved ρ := hcomm A hA hn
      _ ≤ centralizer (fittingSubgroup G : Set G) := hF

/-- Assemble all five clauses after constructing the internal splitting and
its commutator control. The source hypotheses must still produce these inputs. -/
theorem conclusion_of_decomposition (d : Decomposition ρ)
    (hF : fittingMoved ρ ≤ centralizer (fittingSubgroup G : Set G))
    (hcomm : ∀ A, IsMinimalBestOffender ρ A → ⁅fittingSubgroup G, A⁆ ≠ ⊥ →
      ⁅minimalGenerated ρ, A⁆ ≤ fittingMoved ρ) : Nonempty (Conclusion ρ) := by
  refine ⟨{ toDecomposition := d, moved_subgroup_centralizes := ?_ }⟩
  intro A hA K hK
  exact minimal_moved_centralizes_of_control ρ hF hcomm hA hK

/-- The universal B.1.9 implication, with the local-plane and global-splitting
premises discharged from faithfulness and O₂(G) = 1. -/
theorem sourceTheorem : SourceTheorem.{u, v} := by
  intro G _ _ V _ _ _ ρ hρ hcore hF
  have hlocal : LocalPlaneLaw ρ := localPlaneLaw ρ hρ hcore
  obtain ⟨d⟩ := nonempty_decomposition_of_localPlaneLaw ρ hρ hcore hF hlocal
  exact conclusion_of_decomposition ρ d
    (fittingMoved_le_centralizer_fitting ρ hcore hlocal)
    (fun A hA hn => minimalGenerated_commutator_minimal_le_fittingMoved
      ρ hρ hcore hlocal hA hn)

/-- The B.1.10 quotient induction with its universal B.1.9 input discharged. -/
theorem movedFactor_le {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (K A : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K, A⁆) :
    K ≤ offenderSubgroup ρ ⊓ centralizer (fittingSubgroup G : Set G) :=
  MovedFactors.moved_factor_le_of_source ρ sourceTheorem hρ hcore K A hK hA hKA

end CFSG.Quasithin.ChapterB.FittingStructure

namespace CFSG.Quasithin.ChapterB
open Subgroup Representation.BinaryOffender Theory.GroupTheory
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- B.1.9, all five clauses: the actual internal group products, embedded odd
cores, independent rank-two support sum, exact Sylow offender families, and
centralization by every subgroup moved by a minimal best offender. -/
theorem source_lemma_B_1_9 (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hF : FittingStructure.fittingMoved ρ ≠ ⊥) :
    Nonempty (FittingStructure.Conclusion ρ) :=
  FittingStructure.sourceTheorem G V ρ hρ hcore hF

/-- B.1.10: a quasisimple or order-three subgroup moved by any best offender
lies in the centralizer of F(G) inside J(G,V). -/
theorem source_lemma_B_1_10 (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (K A : Subgroup G) (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K, A⁆) :
    K ≤ offenderSubgroup ρ ⊓ centralizer (fittingSubgroup G : Set G) :=
  FittingStructure.movedFactor_le ρ hρ hcore K A hK hA hKA

end CFSG.Quasithin.ChapterB
