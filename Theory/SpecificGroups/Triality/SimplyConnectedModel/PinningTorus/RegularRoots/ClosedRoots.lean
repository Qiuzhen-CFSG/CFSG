module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RootPoints
public import Theory.AlgebraicGroup.Morphism.CodRestrict

/-!
# Closed Spin root subgroups and regular parameter recovery

The inverse image of an Omega root subgroup under the actual regular Spin
cover is closed. In characteristic two, faithfulness of the natural action
identifies its points exactly with the anchored `rootPoint` family.
Composing the restricted cover with the inverse of the checked Omega root
parametrization gives a regular additive parameter on this closed subgroup.

`rootParametrizationOfMorphism` constructs the full algebraic isomorphism
once the forward Spin root morphism, with its exact point formula, is supplied.
The forward regularity hypothesis is explicit: point bijectivity of the Spin
cover is not used to assert an algebraic inverse.

Source: GLS3, §§1.9 and 1.12 (`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup

universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The actual orthogonal target of the Clifford Spin cover. -/
abbrev omegaVariety : Variety k := (cliffordModel k).omega.carrierVariety

/-- The group structure inherited from the closed Omega carrier. -/
instance omegaVarietyAlgebraicGroup : AlgebraicGroup (omegaVariety k) :=
  (cliffordModel k).omega.carrierAlgebraicGroup

/-- The actual regular cover of the fixed Spin carrier. -/
abbrev rootCover : Morphism (groupVariety k) (omegaVariety k) :=
  (cliffordModel k).spinCover

/-- The checked Omega root morphism in the same root normalization. -/
abbrev omegaRootMorphism (r : RootIndex) : Morphism (KPlus k) (omegaVariety k) :=
  evenOrthogonalRootMorphism 4 (show 4 ≤ 4 from le_rfl) r

omit [CharP k 2] in
/-- The Omega morphism has the prescribed quadratic-isometry matrix. -/
theorem omegaPoints_rootMorphism (r : RootIndex) (x : Variety.Point (KPlus k)) :
    ((cliffordModel k).omegaPoints ((omegaRootMorphism k r).onPoints x)).val =
      evenOrthogonalRootQuadraticPoint 4 r (x.val PUnit.unit) := by
  apply Subtype.ext
  rw [← (cliffordModel k).omegaLinear_points]
  change LinearMap.GeneralLinearGroup.generalLinearEquiv k (QuadraticSpace k)
      (glPointEquivOf k (QuadraticSpace k) (Module.finBasis k (QuadraticSpace k))
        ((evenSpinActionImageClosedSubgroup (quadraticForm k)
          (standardHyperbolicSplit 4)).includePoint
          ((evenOrthogonalRootMorphism 4 (show 4 ≤ 4 from le_rfl) r).onPoints x))) = _
  rw [evenOrthogonalRootMorphism_include_apply]
  exact evenOrthogonalRootAmbientMorphism_linear_points 4 r x

/-- The anchored Spin points map to the standard Omega root curve. -/
theorem rootCover_rootPoint (r : RootIndex) (a : k) :
    (rootCover k).onPoints (rootPoint k r a) =
      (omegaRootMorphism k r).onPoints (kPlusPoint a) := by
  apply (cliffordModel k).omegaPoints.injective
  apply Subtype.ext
  change naturalAction k (rootPoint k r a) = _
  rw [naturalAction_rootPoint, omegaPoints_rootMorphism]
  rfl

/-- The characteristic-two cover is injective on points. -/
theorem rootCover_injective : Function.Injective (rootCover k).onPoints := by
  intro x y h
  apply toOmega_injective k
  exact congrArg (cliffordModel k).omegaPoints h

/-- The closed inverse image of the standard Omega root subgroup. -/
def rootClosedSubgroup (r : RootIndex) : ClosedSubgroup (groupVariety k) :=
  (rootCover k).closedSubgroupPreimage (evenOrthogonalRootSubgroup 4 (show 4 ≤ 4 from le_rfl) r)

/-- The inherited algebraic group on the closed root carrier. -/
instance rootClosedSubgroupAlgebraicGroup (r : RootIndex) :
    AlgebraicGroup (rootClosedSubgroup k r).carrierVariety :=
  (rootClosedSubgroup k r).carrierAlgebraicGroup

local instance omegaRootSubgroupAlgebraicGroup (r : RootIndex) :
    AlgebraicGroup (evenOrthogonalRootSubgroup (k := k) 4 (show 4 ≤ 4 from le_rfl) r).carrierVariety :=
  (evenOrthogonalRootSubgroup (k := k) 4 (show 4 ≤ 4 from le_rfl) r).carrierAlgebraicGroup

/-- The closed inverse image has exactly the anchored root points. -/
theorem mem_rootClosedSubgroup_iff (r : RootIndex) (x : Points k) :
    x ∈ rootClosedSubgroup k r ↔ ∃ a : k, rootPoint k r a = x := by
  change (∃ y : Variety.Point (KPlus k),
      (omegaRootMorphism k r).onPoints y = (rootCover k).onPoints x) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y.val PUnit.unit, rootCover_injective k ?_⟩
    rw [rootCover_rootPoint]
    have he : kPlusPoint (y.val PUnit.unit) = y := kPlusPoint_coordinate y
    rw [he]
    exact hy
  · rintro ⟨a, rfl⟩
    exact ⟨kPlusPoint a, (rootCover_rootPoint k r a).symm⟩

/-- Agreement with the original point-subgroup API. -/
theorem rootClosedSubgroup_toSubgroup (r : RootIndex) :
    (rootClosedSubgroup k r).toSubgroup = rootPointSubgroup k r := by
  ext x
  change x ∈ rootClosedSubgroup k r ↔ x ∈ rootPointSubgroup k r
  rw [mem_rootClosedSubgroup_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.ofAdd a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.toAdd, rfl⟩

/-- The original root-point subgroup is Zariski closed. -/
theorem rootPointSubgroup_isZariskiClosed (r : RootIndex) :
    IsZariskiClosed (groupVariety k) (rootPointSubgroup k r : Set (Points k)) := by
  rw [← rootClosedSubgroup_toSubgroup]
  exact (rootClosedSubgroup k r).isZariskiClosed

/-- The anchored root point, now regarded as a point of its closed subgroup. -/
def rootSubgroupPoint (r : RootIndex) (a : k) :
    Variety.Point (rootClosedSubgroup k r).carrierVariety :=
  (rootClosedSubgroup k r).pointEquiv.symm
    ⟨rootPoint k r a, (mem_rootClosedSubgroup_iff k r _).mpr ⟨a, rfl⟩⟩

/-- Inclusion preserves the exact root normalization. -/
@[simp] theorem rootSubgroupPoint_inclusion (r : RootIndex) (a : k) :
    (rootClosedSubgroup k r).inclusion.onPoints (rootSubgroupPoint k r a) =
      rootPoint k r a := by
  exact congrArg Subtype.val ((rootClosedSubgroup k r).pointEquiv.apply_symm_apply _)

/-- Regular recovery of the additive parameter through the Omega root curve. -/
def rootParameter (r : RootIndex) :
    Morphism (rootClosedSubgroup k r).carrierVariety (KPlus k) :=
  (evenOrthogonalRootParametrization 4 (show 4 ≤ 4 from le_rfl) r).inv.comp
    ((rootCover k).preimageRestriction (evenOrthogonalRootSubgroup 4 (show 4 ≤ 4 from le_rfl) r))

omit [CharP k 2] in
/-- Parameter recovery commutes with the actual Spin cover. -/
theorem rootParameter_spec (r : RootIndex)
    (x : Variety.Point (rootClosedSubgroup k r).carrierVariety) :
    (omegaRootMorphism k r).onPoints ((rootParameter k r).onPoints x) =
      (rootCover k).onPoints ((rootClosedSubgroup k r).inclusion.onPoints x) := by
  let Y := evenOrthogonalRootSubgroup (k := k) 4 (show 4 ≤ 4 from le_rfl) r
  let : AlgebraicGroup Y.carrierVariety := Y.carrierAlgebraicGroup
  let : AlgebraicGroup ((rootCover k).closedSubgroupPreimage Y).carrierVariety :=
    ((rootCover k).closedSubgroupPreimage Y).carrierAlgebraicGroup
  let e := evenOrthogonalRootParametrization (k := k) 4 (show 4 ≤ 4 from le_rfl) r
  let q : Morphism (rootClosedSubgroup k r).carrierVariety Y.carrierVariety :=
    (rootCover k).preimageRestriction Y
  have he (z : Variety.Point (KPlus k)) :
      Y.inclusion.onPoints (e.hom.onPoints z) = (omegaRootMorphism k r).onPoints z := by
    rw [evenOrthogonalRootParametrization_hom]
    exact Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  rw [← he]
  change Y.inclusion.onPoints
    (e.hom.onPoints (e.inv.onPoints (q.onPoints x))) = _
  rw [e.inv_hom_id]
  exact Morphism.preimageRestriction_inclusion_apply _ _ _

/-- Recovery returns the original additive parameter. -/
@[simp] theorem rootParameter_rootSubgroupPoint (r : RootIndex) (a : k) :
    (rootParameter k r).onPoints (rootSubgroupPoint k r a) = kPlusPoint a := by
  apply evenOrthogonalRootMorphism_injective 4 (show 4 ≤ 4 from le_rfl) r
  change (omegaRootMorphism k r).onPoints _ = (omegaRootMorphism k r).onPoints _
  rw [rootParameter_spec, rootSubgroupPoint_inclusion, rootCover_rootPoint]

/-- The recovered parameter reconstructs every point of the closed subgroup. -/
theorem rootSubgroupPoint_rootParameter (r : RootIndex)
    (x : Variety.Point (rootClosedSubgroup k r).carrierVariety) :
    rootSubgroupPoint k r (((rootParameter k r).onPoints x).val PUnit.unit) = x := by
  apply (rootClosedSubgroup k r).inclusion_injective
  rw [rootSubgroupPoint_inclusion]
  apply rootCover_injective k
  rw [rootCover_rootPoint]
  have he : kPlusPoint (((rootParameter k r).onPoints x).val PUnit.unit) =
      (rootParameter k r).onPoints x := kPlusPoint_coordinate _
  rw [he, rootParameter_spec]

/-- The normalized point formula at an arbitrary additive-group point. -/
theorem rootMorphism_apply_of_points (r : RootIndex)
    (f : Morphism (KPlus k) (groupVariety k))
    (hf : ∀ a, f.onPoints (kPlusPoint a) = rootPoint k r a)
    (x : Variety.Point (KPlus k)) :
    f.onPoints x = rootPoint k r (x.val PUnit.unit) := by
  have h := hf (x.val PUnit.unit)
  rwa [show kPlusPoint (x.val PUnit.unit) = x from kPlusPoint_coordinate x] at h

/-- Any normalized regular root curve intertwines the actual Spin cover. -/
theorem rootMorphism_cover_of_points (r : RootIndex)
    (f : Morphism (KPlus k) (groupVariety k))
    (hf : ∀ a, f.onPoints (kPlusPoint a) = rootPoint k r a) :
    (rootCover k).comp f = omegaRootMorphism k r := by
  apply Morphism.ext
  funext x
  change (rootCover k).onPoints (f.onPoints x) = _
  rw [rootMorphism_apply_of_points k r f hf, rootCover_rootPoint]
  rw [show kPlusPoint (x.val PUnit.unit) = x from kPlusPoint_coordinate x]
  rfl

/-- A normalized forward morphism and regular recovery give an algebraic
isomorphism, without an algebraic inverse to the ambient cover. -/
def rootParametrizationOfMorphism (r : RootIndex)
    (f : Morphism (KPlus k) (groupVariety k))
    (hf : ∀ a, f.onPoints (kPlusPoint a) = rootPoint k r a) :
    OneParameterParametrization (rootClosedSubgroup k r).carrierVariety := by
  let hmem : ∀ x, f.onPoints x ∈ (rootClosedSubgroup k r).toSubgroup := fun x => by
    apply (mem_rootClosedSubgroup_iff k r _).mpr
    exact ⟨x.val PUnit.unit, (rootMorphism_apply_of_points k r f hf x).symm⟩
  let g := f.codRestrictClosedSubgroup (rootClosedSubgroup k r) hmem
  have hg (x) : (rootClosedSubgroup k r).inclusion.onPoints (g.onPoints x) =
      f.onPoints x := Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hcover (x) : (rootCover k).onPoints (f.onPoints x) =
      (omegaRootMorphism k r).onPoints x :=
    congrArg (fun q : Morphism (KPlus k) (omegaVariety k) => q.onPoints x)
      (rootMorphism_cover_of_points k r f hf)
  exact {
    hom := g
    inv := rootParameter k r
    hom_inv_id := by
      intro x
      apply evenOrthogonalRootMorphism_injective 4 (show 4 ≤ 4 from le_rfl) r
      change (omegaRootMorphism k r).onPoints _ = (omegaRootMorphism k r).onPoints _
      rw [rootParameter_spec, hg, hcover]
    inv_hom_id := by
      intro x
      apply (rootClosedSubgroup k r).inclusion_injective
      apply rootCover_injective k
      rw [hg, hcover, rootParameter_spec]
  }

/-- The resulting one-parameter isomorphism has the original inclusion formula. -/
theorem rootParametrizationOfMorphism_inclusion (r : RootIndex)
    (f : Morphism (KPlus k) (groupVariety k))
    (hf : ∀ a, f.onPoints (kPlusPoint a) = rootPoint k r a) (a : k) :
    (rootClosedSubgroup k r).includePoint
      ((rootParametrizationOfMorphism k r f hf).value a) = rootPoint k r a := by
  change (rootClosedSubgroup k r).inclusion.onPoints
    ((f.codRestrictClosedSubgroup (rootClosedSubgroup k r) _).onPoints (kPlusPoint a)) = _
  rw [Morphism.codRestrictClosedSubgroup_inclusion_apply, hf]

end Triality.SimplyConnected.Pinning
