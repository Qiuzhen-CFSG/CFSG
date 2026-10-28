module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.ClosedRoots
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.TorusCoordinates

/-!
# Torus invariance and normalized Spin root weights

The geometric simple-coroot coordinates normalize each closed Spin root
subgroup. Once a forward regular root curve is supplied, the checked parameter
recovery constructs its one-parameter isomorphism. The point conjugation
formula then holds for every algebraic parametrization, since any two differ
by a nonzero scalar. Thus each proposed character is an actual torus root.

These are conditional construction lemmas. Exhaustiveness of the displayed
characters and construction of the forward regular curves are not assumed to
be proved here. Source: GLS3, §§1.9 and 1.12.
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup

universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

local instance rootActionTorusAlgebraicGroup (T : ClosedSubgroup (groupVariety k)) :
    AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup

/-- The coroot coordinate formula makes every closed root subgroup invariant. -/
theorem rootClosedSubgroup_invariant (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety)
    (he : HasCorootCoordinates k T e) (r : RootIndex) :
    IsClosedSubgroupInvariant T (rootClosedSubgroup k r) := by
  intro t ht x hx
  obtain ⟨a, rfl⟩ := (mem_rootClosedSubgroup_iff k r x).mp hx
  let s : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
  have hs : T.includePoint s = t :=
    congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨t, ht⟩)
  rw [← hs, coordinateRootWeight_conjugation k T e he]
  exact (mem_rootClosedSubgroup_iff k r _).mpr ⟨_, rfl⟩

/-- Any normalized forward regular curve proves the full root-weight equation,
including its quantification over all one-parameter parametrizations. -/
theorem coordinateRootWeight_equation_of_morphism
    (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety)
    (he : HasCorootCoordinates k T e) (r : RootIndex)
    (f : Morphism (KPlus k) (groupVariety k))
    (hf : ∀ a, f.onPoints (kPlusPoint a) = rootPoint k r a) :
    RootWeightEquation T (rootClosedSubgroup k r) (coordinateRootWeight k T e r) := by
  intro y a s
  let p := rootParametrizationOfMorphism k r f hf
  obtain ⟨c, hc, _⟩ := oneParameterParametrization_eq_rescale p y
  have hy (b : k) :
      (rootClosedSubgroup k r).includePoint (y.value b) = rootPoint k r (c * b) := by
    rw [hc.2]
    exact rootParametrizationOfMorphism_inclusion k r f hf (c * b)
  rw [hy, hy, coordinateRootWeight_conjugation k T e he]
  congr 1
  ring

/-- A normalized regular root morphism makes its coordinate character an
actual root of the geometric torus. -/
theorem coordinateRootWeight_mem_torusRootSet_of_morphism
    (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety)
    (he : HasCorootCoordinates k T e) (r : RootIndex)
    (f : Morphism (KPlus k) (groupVariety k))
    (hf : ∀ a, f.onPoints (kPlusPoint a) = rootPoint k r a) :
    coordinateRootWeight k T e r ∈ TorusRootSet T :=
  ⟨rootClosedSubgroup k r,
    ⟨rootClosedSubgroup_invariant k T e he r,
      ⟨rootParametrizationOfMorphism k r f hf⟩⟩,
    coordinateRootWeight_equation_of_morphism k T e he r f hf⟩

end Triality.SimplyConnected.Pinning
