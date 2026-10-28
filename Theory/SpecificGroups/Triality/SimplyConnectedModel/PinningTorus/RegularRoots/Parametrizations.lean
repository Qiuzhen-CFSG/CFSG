module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.CliffordCurves

/-!
# Normalized algebraic parametrizations of the Spin D4 root subgroups

The explicit Clifford root curves and the regular Omega parameter recovery
are mutually inverse on the closed Spin root subgroups. Thus the anchored
root points give genuine one-parameter algebraic isomorphisms, with exactly
the published parameter. The regular Spin cover intertwines these
parametrizations with the existing Omega root parametrizations.

Source: GLS3, Definitions 1.9.1–3 and the normalization of 1.12.1
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

local instance parametrizedRootsOmegaAlgebraicGroup (r : RootIndex) :
    AlgebraicGroup (evenOrthogonalRootSubgroup (k := k) 4 (le_refl 4) r).carrierVariety :=
  (evenOrthogonalRootSubgroup (k := k) 4 (le_refl 4) r).carrierAlgebraicGroup

/-- The normalized algebraic isomorphism from the additive group onto a Spin root subgroup. -/
def rootParametrization (r : RootIndex) :
    OneParameterParametrization (rootClosedSubgroup k r).carrierVariety :=
  rootParametrizationOfMorphism k r (cliffordRootMorphism k r)
    (cliffordRootMorphism_kPlusPoint k r)

@[simp] theorem rootParametrization_inclusion (r : RootIndex) (a : k) :
    (rootClosedSubgroup k r).includePoint ((rootParametrization k r).value a) =
      rootPoint k r a :=
  rootParametrizationOfMorphism_inclusion k r _ _ a

theorem rootClosedSubgroup_isOneParameter (r : RootIndex) :
    IsOneParameterGroup (rootClosedSubgroup k r).carrierVariety :=
  ⟨rootParametrization k r⟩

theorem rootParametrization_cover (r : RootIndex) (a : k) :
    (rootCover k).onPoints
      ((rootClosedSubgroup k r).includePoint ((rootParametrization k r).value a)) =
    (evenOrthogonalRootSubgroup 4 (le_refl 4) r).includePoint
      ((evenOrthogonalRootParametrization 4 (le_refl 4) r).value a) := by
  rw [rootParametrization_inclusion, rootCover_rootPoint]
  change _ = (evenOrthogonalRootSubgroup 4 (le_refl 4) r).inclusion.onPoints
    ((evenOrthogonalRootParametrization 4 (le_refl 4) r).hom.onPoints (kPlusPoint a))
  rw [evenOrthogonalRootParametrization_hom]
  exact (Morphism.codRestrictClosedSubgroup_inclusion_apply
    (evenOrthogonalRootMorphism (k := k) 4 (le_refl 4) r)
    (evenOrthogonalRootSubgroup (k := k) 4 (le_refl 4) r) _ (kPlusPoint a)).symm

end Triality.SimplyConnected.Pinning
