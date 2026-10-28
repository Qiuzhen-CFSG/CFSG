module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Products
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Representatives

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Products
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.InvolutionRepresentatives
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Recognition from the source marked chamber: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Representatives` proof for the local step.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

open scoped Pointwise in
/-- The marked chamber discharges both intrinsic involution inputs to recognition. -/
theorem isPSp_of_source_marked_chamber_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (hnormal : H₀ ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (supplement : ∀ X : Subgroup G, X ∈ Chapter1.HOver G (H₀ : Set G) →
      (X : Set G) = (H₀ : Set G) *
        (X ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H₀ : Set G) : Subgroup G)) :
    ClassicalGroup.IsPSp G 3 2 := by
  apply isPSp_of_source_thompson_representatives_at h₀ h structural D m z H₀ C hnormal supplement
  exact original_plane_core_representative D z H₀ C
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
