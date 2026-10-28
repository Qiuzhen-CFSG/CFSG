module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.Defs
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Theory.AlgebraicGroup.Variety.ClosedLocus

/-!
# Complete geometric models from closed orbits

A regular action restricts to a reduced closed locus preserved on rational points:
closed-point density proves that the whole action morphism lands in that locus,
and the universal property of the reduced closed subscheme gives the restriction.
For a locus whose rational points form one orbit, this yields a transitive
complete model with the original point stabilizer.

This is the geometric-to-homogeneous-space bridge in Borel, *Linear Algebraic
Groups*, §11.1. Closedness of the chosen flag orbit is an explicit remaining
input, rather than a consequence of the model interface.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem range_subset_closed_of_points
    {V W : Geometric k} (f : Morphism V W) (Z : Closeds W.toScheme)
    (h : ∀ x : Point V, (f x).1 (IsLocalRing.closedPoint k) ∈ Z) :
    Set.range f.hom ⊆ Z := by
  rintro _ ⟨z, rfl⟩
  by_contra hz
  let U : Set V.toScheme := (f.hom ⁻¹' Z)ᶜ
  have hU : IsOpen U := (Z.isClosed.preimage f.hom.continuous).isOpen_compl
  let : JacobsonSpace V.toScheme :=
    LocallyOfFiniteType.jacobsonSpace V.structureMap
  obtain ⟨y, hyU, hyclosed⟩ :=
    nonempty_inter_closedPoints (show U.Nonempty from ⟨z, hz⟩) hU.isLocallyClosed
  let p : Point V := (pointEquivClosedPoint V.structureMap).symm ⟨y, hyclosed⟩
  have hp : p.1 (IsLocalRing.closedPoint k) = y :=
    congrArg Subtype.val ((pointEquivClosedPoint V.structureMap).apply_symm_apply _)
  have hh := h p
  change f.hom (p.1 (IsLocalRing.closedPoint k)) ∈ Z at hh
  rw [hp] at hh
  exact hyU hh

omit [IsAlgClosed k] in
private theorem closedInclusion_injective {V : Geometric k} (C : ClosedSubvariety V) :
    Function.Injective C.inclusion := by
  intro x y hxy
  apply Subtype.ext
  apply (cancel_mono C.inclusion.hom).mp
  exact congrArg Subtype.val hxy

omit [IsAlgClosed k] in
private theorem closedInclusion_mem {V : Geometric k} (Z : Closeds V.toScheme)
    (x : Point (reducedClosedSubvariety V Z).toGeometric) :
    ((reducedClosedSubvariety V Z).inclusion x).1 (IsLocalRing.closedPoint k) ∈ Z := by
  apply (point_mem_reducedClosedSubvariety_iff V Z _).mpr
  exact ⟨x, rfl, fun y hy => closedInclusion_injective _ hy⟩

namespace MorphicAction

variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X : Geometric k}

private noncomputable def restrictedActionToAmbient
    (A : MorphicAction G X) (Z : Closeds X.toScheme) :
    Morphism (prod (ofAffine G) (reducedClosedSubvariety X Z).toGeometric) X :=
  Morphism.comp
    (Morphism.pair (fst _ _)
      (Morphism.comp (snd _ _) (reducedClosedSubvariety X Z).inclusion))
    A.actionMorphism

private theorem restrictedActionToAmbient_apply
    (A : MorphicAction G X) (Z : Closeds X.toScheme)
    (g : Theory.AlgebraicGroup.Variety.Point G)
    (y : Point (reducedClosedSubvariety X Z).toGeometric) :
    restrictedActionToAmbient A Z (prodPoint ((affinePointEquiv G).symm g) y) =
      A.toMulAction.smul g ((reducedClosedSubvariety X Z).inclusion y) := by
  unfold restrictedActionToAmbient
  erw [Morphism.comp_apply_point, Morphism.pair_apply, fst_prodPoint,
    Morphism.comp_apply_point, snd_prodPoint]
  exact A.actionMorphism_apply g _

/-- Restrict a morphic action to an invariant reduced closed locus. Invariance
only needs checking on rational points: these are dense in every geometric source. -/
public noncomputable def onInvariantReducedClosedSubvariety
    (A : MorphicAction G X) (Z : Closeds X.toScheme)
    (hZ : ∀ (g : Theory.AlgebraicGroup.Variety.Point G) (x : Point X),
      x.1 (IsLocalRing.closedPoint k) ∈ Z →
        (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈ Z) :
    MorphicAction G (reducedClosedSubvariety X Z).toGeometric := by
  classical
  let := A.toMulAction
  let C := reducedClosedSubvariety X Z
  have hlift (g : Theory.AlgebraicGroup.Variety.Point G) (y : Point C.toGeometric) :
      ∃ z : Point C.toGeometric, C.inclusion z = A.toMulAction.smul g (C.inclusion y) := by
    obtain ⟨z, hz, _⟩ := (point_mem_reducedClosedSubvariety_iff X Z _).mp
      (hZ g (C.inclusion y) (closedInclusion_mem Z y))
    exact ⟨z, hz⟩
  let s := fun g y => (hlift g y).choose
  have hs (g : Theory.AlgebraicGroup.Variety.Point G) (y : Point C.toGeometric) :
      C.inclusion (s g y) = A.toMulAction.smul g (C.inclusion y) := (hlift g y).choose_spec
  let f := restrictedActionToAmbient A Z
  have hf : Set.range f.hom ⊆ Z := by
    apply range_subset_closed_of_points
    intro z
    obtain ⟨⟨a, y⟩, rfl⟩ := (prodPointEquiv (ofAffine G) C.toGeometric).symm.surjective z
    let g := affinePointEquiv G a
    have ha : a = (affinePointEquiv G).symm g := by simp [g]
    change (f (prodPoint a y)).1 (IsLocalRing.closedPoint k) ∈ Z
    rw [ha, restrictedActionToAmbient_apply]
    exact hZ g (C.inclusion y) (closedInclusion_mem Z y)
  let fZ := restrictToReducedClosedSubvariety Z f hf
  have hfac : Morphism.comp fZ C.inclusion = f :=
    restrictToReducedClosedSubvariety_inclusion Z f hf
  exact
    { smul := s
      one_smul := by
        intro y
        apply closedInclusion_injective C
        erw [hs]
        exact @one_smul _ _ _ A.toMulAction _
      mul_smul := by
        intro g h y
        apply closedInclusion_injective C
        erw [hs, hs, hs]
        exact @mul_smul _ _ _ A.toMulAction.toSemigroupAction _ _ _
      actionMorphism := fZ
      actionMorphism_apply := by
        intro g y
        apply closedInclusion_injective C
        rw [hs]
        change Morphism.comp fZ C.inclusion
          (prodPoint ((affinePointEquiv G).symm g) y) = _
        rw [hfac]
        exact restrictedActionToAmbient_apply A Z g y }

public theorem onInvariantReducedClosedSubvariety_inclusion
    (A : MorphicAction G X) (Z : Closeds X.toScheme)
    (hZ : ∀ (g : Theory.AlgebraicGroup.Variety.Point G) (x : Point X),
      x.1 (IsLocalRing.closedPoint k) ∈ Z →
        (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈ Z)
    (g : Theory.AlgebraicGroup.Variety.Point G)
    (y : Point (reducedClosedSubvariety X Z).toGeometric) :
    (reducedClosedSubvariety X Z).inclusion
        ((A.onInvariantReducedClosedSubvariety Z hZ).toMulAction.smul g y) =
      A.toMulAction.smul g ((reducedClosedSubvariety X Z).inclusion y) := by
  let C := reducedClosedSubvariety X Z
  have h : ∃ z : Point C.toGeometric,
      C.inclusion z = A.toMulAction.smul g (C.inclusion y) :=
    ((point_mem_reducedClosedSubvariety_iff X Z _).mp
      (hZ g (C.inclusion y) (closedInclusion_mem Z y))).exists
  change C.inclusion (Classical.choose h) = _
  exact Classical.choose_spec h

end MorphicAction
end Theory.AlgebraicGroup.Variety.Geometric

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy

open Variety.Geometric

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- A closed orbit in a complete variety whose stabilizer is `B` gives a complete
geometric model of `G / B`. The support hypothesis identifies the whole orbit,
and the action on its reduced closed subvariety is constructed by restriction. -/
public theorem nonempty_completeModel_of_closed_orbit_support
    (B : ClosedSubgroup G) {X : Variety.Geometric k} (A : MorphicAction G X)
    (x : Point X) (hcomplete : IsComplete X) (Z : Closeds X.toScheme)
    (horbit : ∀ y : Point X, y.1 (IsLocalRing.closedPoint k) ∈ Z ↔
      ∃ g : Variety.Point G, A.toMulAction.smul g x = y)
    (hstab : ∀ g : Variety.Point G, A.toMulAction.smul g x = x ↔ g ∈ B.toSubgroup) :
    Nonempty (CompleteModel B) := by
  let := A.toMulAction
  have hZ (g : Variety.Point G) (y : Point X)
      (hy : y.1 (IsLocalRing.closedPoint k) ∈ Z) :
      (A.toMulAction.smul g y).1 (IsLocalRing.closedPoint k) ∈ Z := by
    obtain ⟨h, rfl⟩ := (horbit y).mp hy
    exact (horbit _).mpr ⟨g * h, mul_smul g h x⟩
  let C := reducedClosedSubvariety X Z
  let R := A.onInvariantReducedClosedSubvariety Z hZ
  have hCx : x.1 (IsLocalRing.closedPoint k) ∈ Z :=
    (horbit x).mpr ⟨1, one_smul _ x⟩
  obtain ⟨x', hx', _⟩ := (point_mem_reducedClosedSubvariety_iff X Z x).mp hCx
  have hinj : Function.Injective C.inclusion := by
    intro a b hab
    apply Subtype.ext
    apply (cancel_mono C.inclusion.hom).mp
    exact congrArg Subtype.val hab
  have heq (g : Variety.Point G) (y : Point C.toGeometric) :
      C.inclusion (R.toMulAction.smul g y) = A.toMulAction.smul g (C.inclusion y) :=
    A.onInvariantReducedClosedSubvariety_inclusion Z hZ g y
  have htrans (y : Point C.toGeometric) :
      ∃ g : Variety.Point G, R.toMulAction.smul g x' = y := by
    have hy : (C.inclusion y).1 (IsLocalRing.closedPoint k) ∈ Z :=
      (point_mem_reducedClosedSubvariety_iff X Z _).mpr
        ⟨y, rfl, fun z hz => hinj hz⟩
    obtain ⟨g, hg⟩ := (horbit (C.inclusion y)).mp hy
    refine ⟨g, hinj ?_⟩
    erw [heq, hx']
    exact hg
  have hstab' (g : Variety.Point G) :
      R.toMulAction.smul g x' = x' ↔ g ∈ B.toSubgroup := by
    have hh : C.inclusion (R.toMulAction.smul g x') = A.toMulAction.smul g x := by
      exact (heq g x').trans (congrArg (A.toMulAction.smul g) hx')
    constructor
    · intro hfix
      apply (hstab g).mp
      exact hh.symm.trans ((congrArg C.inclusion hfix).trans hx')
    · intro hg
      apply hinj
      exact hh.trans (((hstab g).mpr hg).trans hx'.symm)
  exact ⟨CompleteModel.ofTransitive B R x'
    (C.isComplete hcomplete) htrans hstab'⟩

end Theory.AlgebraicGroup.BorelGeometricConjugacy
