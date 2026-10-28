module

public import Theory.AlgebraicGroup.Variety.Complete
public import Theory.AlgebraicGroup.Variety.OpenSubvariety

/-!
# Escape from affine charts

A map from a connected complete geometric variety to an affine geometric
variety is constant. The scheme image is proper and affine over the field,
hence finite; connectedness makes its underlying space a singleton. Therefore
a nonconstant complete connected image meets the complement of every affine
open. This is the hyperplane-escape step of Borel, §§13.5–13.6.
-/

public noncomputable section

set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k]

theorem morphism_to_geometric_affine_constant [IsAlgClosed k]
    {V W : Geometric k} [IsAffine W.toScheme]
    (f : Morphism V W) (hVconnected : IsConnected V)
    (hVcomplete : IsComplete V) :
    ∀ x y : Point V, f x = f y := by
  letI : ConnectedSpace V.toScheme := hVconnected
  letI : UniversallyClosed V.structureMap := hVcomplete
  letI : UniversallyClosed (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  letI : UniversallyClosed f.hom :=
    UniversallyClosed.of_comp_of_isSeparated f.hom W.structureMap
  letI : Surjective f.hom.toImage :=
    Surjective.of_universallyClosed_of_isDominant f.hom.toImage
  let q := f.hom.imageι ≫ W.structureMap
  letI : UniversallyClosed (f.hom.toImage ≫ q) := by
    dsimp only [q]
    rw [f.hom.toImage_imageι_assoc, f.commutes]
    infer_instance
  letI : UniversallyClosed q :=
    UniversallyClosed.of_comp_surjective f.hom.toImage q
  letI : IsProper q := IsProper.mk
  letI : IsAffine f.hom.image := isAffine_of_isAffineHom f.hom.imageι
  letI : IsAffineHom q := isAffineHom_of_isAffine q
  letI : IsFinite q :=
    (IsFinite.iff_isProper_and_isAffineHom (f := q)).mpr ⟨inferInstance, inferInstance⟩
  letI : ConnectedSpace f.hom.image :=
    f.hom.toImage.surjective.connectedSpace f.hom.toImage.continuous
  have hpreimage : q ⁻¹' {IsLocalRing.closedPoint k} =
      (Set.univ : Set f.hom.image) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hdiscrete : DiscreteTopology f.hom.image := by
    rw [← isDiscrete_univ_iff, ← hpreimage]
    exact q.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)
  letI : DiscreteTopology f.hom.image := hdiscrete
  letI : Subsingleton f.hom.image :=
    subsingleton_of_preconnected_totallyDisconnected
  intro x y
  apply Subtype.ext
  apply ext_of_apply_closedPoint_eq W.structureMap
      (f x).2 (f y).2
  change (x.1 ≫ f.hom) (IsLocalRing.closedPoint k) =
    (y.1 ≫ f.hom) (IsLocalRing.closedPoint k)
  rw [← f.hom.toImage_imageι]
  change f.hom.imageι (f.hom.toImage (x.1 (IsLocalRing.closedPoint k))) =
    f.hom.imageι (f.hom.toImage (y.1 (IsLocalRing.closedPoint k)))
  congr 1
  exact Subsingleton.elim _ _


/-- A morphism whose rational points lie in an open locus factors through it. -/
theorem Morphism.range_subset_open_of_points [IsAlgClosed k]
    {V W : Geometric k} (f : Morphism V W) (U : W.toScheme.Opens)
    (h : ∀ x : Point V, (f x).1 (IsLocalRing.closedPoint k) ∈ U) :
    Set.range f.hom ⊆ U := by
  rintro _ ⟨z, rfl⟩
  by_contra hz
  let Z : Set V.toScheme := (f.hom ⁻¹' (U : Set W.toScheme))ᶜ
  have hZ : IsClosed Z := (U.isOpen.preimage f.hom.continuous).isClosed_compl
  letI : JacobsonSpace V.toScheme := LocallyOfFiniteType.jacobsonSpace V.structureMap
  obtain ⟨y, hyZ, hyclosed⟩ :=
    nonempty_inter_closedPoints (show Z.Nonempty from ⟨z, hz⟩) hZ.isLocallyClosed
  let p : Point V := (pointEquivClosedPoint V.structureMap).symm ⟨y, hyclosed⟩
  have hp : p.1 (IsLocalRing.closedPoint k) = y :=
    congrArg Subtype.val ((pointEquivClosedPoint V.structureMap).apply_symm_apply _)
  have hh := h p
  change f.hom (p.1 (IsLocalRing.closedPoint k)) ∈ U at hh
  rw [hp] at hh
  exact hyZ hh

/-- A nonconstant complete connected image cannot be contained in an affine open. -/
theorem Morphism.exists_point_outside_affine_open [IsAlgClosed k]
    {V W : Geometric k} (f : Morphism V W)
    (hVconnected : IsConnected V) (hVcomplete : IsComplete V)
    (U : W.toScheme.Opens) [IsAffine U.toScheme]
    (x y : Point V) (hxy : f x ≠ f y) :
    ∃ z : Point V, (f z).1 (IsLocalRing.closedPoint k) ∉ U := by
  by_contra! h
  let g := restrictToOpenSubvariety U f (f.range_subset_open_of_points U h)
  haveI : IsAffine (openSubvariety W U).toGeometric.toScheme :=
    (inferInstance : IsAffine U.toScheme)
  have hc := morphism_to_geometric_affine_constant g hVconnected hVcomplete x y
  apply hxy
  have hfac := restrictToOpenSubvariety_inclusion U f (f.range_subset_open_of_points U h)
  have he := congrArg (openSubvariety W U).inclusion hc
  change (g.comp (openSubvariety W U).inclusion) x =
    (g.comp (openSubvariety W U).inclusion) y at he
  simpa only [g, hfac] using he

end Theory.AlgebraicGroup.Variety.Geometric
