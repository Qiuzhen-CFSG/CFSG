module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.Assembly
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.FixedKernel
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.SourceAction
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.SmallSupport

/-!
# Minimal-offender Fitting planes: assembly and the small-support consumer

The fixed-space kernel calculation supplies the Thompson A × B step for
F_A on C_V(C_A(F_A)). The source action reduction constructs the faithful
solvable image on W, including its exact relative kernel and trivial two-core.
Restriction and solvable FF structure then eliminate C_A(F_A) and recover
every plane field for the original subgroup F_A A.

`localPlaneLaw` assembles this argument from ambient faithfulness and the
trivial two-core. Its application feeds the actual planes to the independent
cubic-factor decomposition of D.2.12, using precisely the original
minimal-offender family. The earlier conditional interfaces remain available;
the full B.1.9 splitting is assembled separately.
Source: Aschbacher–Smith, B.1.9, printed p.71 (PDF p.82), first proof paragraph.
-/

public section

namespace CFSG.Quasithin.ChapterB.FittingStructure
open Subgroup Representation.BinaryOffender MinimalPlanes
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Conditional assembly from the fixed-space action reductions. -/
theorem localPlaneLaw_of_sourceReductions (hf : Function.Injective ρ)
    (hred : ∀ A, IsMinimalBestOffender ρ A → oddPart A ≠ ⊥ → SourceReduction ρ A) :
    LocalPlaneLaw ρ := by
  intro A hA hn
  exact minimalFittingPlane_of_reduction ρ hf hA hn (hred A hA hn)

/-- Conditional application to the D.2.12 small-support decomposition. -/
theorem minimalMovedFactors_decomposition_of_sourceReductions (hf : Function.Injective ρ)
    (hred : ∀ A, IsMinimalBestOffender ρ A → oddPart A ≠ ⊥ → SourceReduction ρ A) :
    iSupIndep (fun X : minimalMovedFactors ρ => X.val) ∧
    (∀ X ∈ minimalMovedFactors ρ, ∀ Y ∈ minimalMovedFactors ρ,
      X ≤ centralizer (Y : Set G)) ∧
    iSupIndep (fun X : minimalMovedFactors ρ => subspaceCommutator ρ ⊤ X.val) ∧
    fittingMoved ρ = (⨆ X : minimalMovedFactors ρ, X.val) ∧
    subspaceCommutator ρ ⊤ (fittingMoved ρ) =
      ⨆ X : minimalMovedFactors ρ, subspaceCommutator ρ ⊤ X.val :=
  minimalMovedFactors_decomposition ρ hf (localPlaneLaw_of_sourceReductions ρ hf hred)

/-- The first paragraph of B.1.9: every minimal best offender moving F(G)
has an actual faithful S₃ plane, with actor order two and odd factor order three.
No solvability or fixed-space reduction premise is imposed on the ambient group. -/
theorem localPlaneLaw (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥) :
    LocalPlaneLaw ρ :=
  localPlaneLaw_of_sourceReductions ρ hf
    (fun _ hA hn => sourceReduction ρ hf hcore hA hn)

/-- Discharge the local-plane premise in the D.2.12 application to the
original family of nontrivial minimal-offender Fitting commutators. -/
theorem minimalMovedFactors_decomposition_of_trivial_twoCore (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) :
    iSupIndep (fun X : minimalMovedFactors ρ => X.val) ∧
    (∀ X ∈ minimalMovedFactors ρ, ∀ Y ∈ minimalMovedFactors ρ,
      X ≤ centralizer (Y : Set G)) ∧
    iSupIndep (fun X : minimalMovedFactors ρ => subspaceCommutator ρ ⊤ X.val) ∧
    fittingMoved ρ = (⨆ X : minimalMovedFactors ρ, X.val) ∧
    subspaceCommutator ρ ⊤ (fittingMoved ρ) =
      ⨆ X : minimalMovedFactors ρ, subspaceCommutator ρ ⊤ X.val :=
  minimalMovedFactors_decomposition ρ hf (localPlaneLaw ρ hf hcore)

end CFSG.Quasithin.ChapterB.FittingStructure
