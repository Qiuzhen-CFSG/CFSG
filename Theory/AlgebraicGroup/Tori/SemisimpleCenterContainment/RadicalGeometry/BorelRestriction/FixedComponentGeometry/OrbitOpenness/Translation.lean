module

public import Theory.AlgebraicGroup.Bor1.MorphicActionOrbitRange
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Propagating openness along translations

One nonempty source-open patch on which an orbit morphism is open suffices to
make the whole orbit morphism open. Left translates of the patch cover all
closed points of the group and hence all scheme points. Equivariance transports
openness to each translate. A flat patch supplies the initial openness by the
finite-presentation open mapping theorem, without any separability assumption.

This is the homogeneous-quotient input to Borel, *Linear Algebraic Groups*,
§11.15 (`refs/KGroup/Bor1/Chapter4.tex`). Existence of the flat patch is a
separate generic-flatness input.
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open Theory.AlgebraicGroup

private theorem isOpenMap_of_translates
    {E D I : Type*} [TopologicalSpace E] [TopologicalSpace D]
    (f : E → D) (e : I → E ≃ₜ E) (t : I → D ≃ₜ D)
    (he : ∀ i z, f (e i z) = t i (f z))
    (U : Set E) (hU : IsOpen U)
    (hcover : ∀ z, ∃ i, z ∈ e i '' U)
    (hpatch : ∀ V, IsOpen V → V ⊆ U → IsOpen (f '' V)) :
    IsOpenMap f := by
  intro V hV
  have him : f '' V = ⋃ i, t i '' (f '' (U ∩ e i ⁻¹' V)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨i, w, hw, rfl⟩ := hcover z
      exact Set.mem_iUnion.mpr ⟨i, f w, ⟨w, ⟨hw, hz⟩, rfl⟩, (he i w).symm⟩
    · intro hy
      obtain ⟨i, _, ⟨w, hw, rfl⟩, rfl⟩ := Set.mem_iUnion.mp hy
      exact ⟨e i w, hw.2, he i w⟩
  rw [him]
  exact isOpen_iUnion fun i => (t i).isOpenMap _
    (hpatch _ (hU.inter (hV.preimage (e i).continuous)) Set.inter_subset_left)

namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X : Geometric k} (A : MorphicAction G X) (x : Point X)

omit [IsAlgClosed k] in
private theorem left_mul_inv_comp (g : Theory.AlgebraicGroup.Variety.Point G) :
    (leftMulMorphism G g⁻¹).comp (leftMulMorphism G g) =
      Theory.AlgebraicGroup.Variety.Morphism.id G := by
  apply Theory.AlgebraicGroup.Variety.Morphism.ext
  funext h
  simp only [Theory.AlgebraicGroup.Variety.Morphism.comp, leftMulMorphism_apply,
    Theory.AlgebraicGroup.Variety.Morphism.id]
  simp

private noncomputable def leftTranslationIso (g : Theory.AlgebraicGroup.Variety.Point G) :
    (ofAffine G).toScheme ≅ (ofAffine G).toScheme where
  hom := (ofAffine_morphism (leftMulMorphism G g)).hom
  inv := (ofAffine_morphism (leftMulMorphism G g⁻¹)).hom
  hom_inv_id := by
    have h := congrArg Morphism.hom
      (ofAffine_morphism_comp (leftMulMorphism G g⁻¹) (leftMulMorphism G g))
    rw [left_mul_inv_comp, ofAffine_morphism_id] at h
    exact h.symm
  inv_hom_id := by
    have h := congrArg Morphism.hom
      (ofAffine_morphism_comp (leftMulMorphism G g) (leftMulMorphism G g⁻¹))
    have hi := left_mul_inv_comp (G := G) g⁻¹
    simp only [inv_inv] at hi
    rw [hi, ofAffine_morphism_id] at h
    exact h.symm

private theorem leftTranslation_closedPoint
    (g : Theory.AlgebraicGroup.Variety.Point G) (p : Point (ofAffine G)) :
    (leftTranslationIso g).hom (p.1 (IsLocalRing.closedPoint k)) =
      (((affinePointEquiv G).symm (g * affinePointEquiv G p)).1
        (IsLocalRing.closedPoint k)) := by
  have hp : ofAffine_morphism (leftMulMorphism G g) p =
      (affinePointEquiv G).symm (g * affinePointEquiv G p) := by
    apply (affinePointEquiv G).injective
    rw [affinePointEquiv_ofAffine_morphism, Equiv.apply_symm_apply]
    exact leftMulMorphism_apply G g _
  exact congrArg (fun q : Point (ofAffine G) => q.1 (IsLocalRing.closedPoint k)) hp

private theorem translates_cover (U : Set (ofAffine G).toScheme)
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∀ z, ∃ g : Theory.AlgebraicGroup.Variety.Point G,
      z ∈ (Scheme.homeoOfIso (leftTranslationIso g)) '' U := by
  let W : Set (ofAffine G).toScheme :=
    ⋃ g : Theory.AlgebraicGroup.Variety.Point G,
      (Scheme.homeoOfIso (leftTranslationIso g)) '' U
  have hW : IsOpen W := isOpen_iUnion fun g =>
    (Scheme.homeoOfIso (leftTranslationIso g)).isOpenMap U hU
  obtain ⟨p, hp⟩ := exists_point_closedPoint_mem_of_isOpen (ofAffine G) hU hne
  letI : JacobsonSpace (ofAffine G).toScheme :=
    LocallyOfFiniteType.jacobsonSpace (ofAffine G).structureMap
  have hcp : closedPoints (ofAffine G).toScheme ⊆ W := by
    intro z hz
    let q : Point (ofAffine G) :=
      (pointEquivClosedPoint (ofAffine G).structureMap).symm ⟨z, hz⟩
    have hq : q.1 (IsLocalRing.closedPoint k) = z :=
      congrArg Subtype.val ((pointEquivClosedPoint (ofAffine G).structureMap).apply_symm_apply ⟨z, hz⟩)
    let g := affinePointEquiv G q * (affinePointEquiv G p)⁻¹
    refine Set.mem_iUnion.mpr ⟨g, p.1 (IsLocalRing.closedPoint k), hp, ?_⟩
    change (leftTranslationIso g).hom _ = z
    rw [leftTranslation_closedPoint]
    simpa [g] using hq
  intro z
  have hz : z ∈ W := by
    by_contra hz
    obtain ⟨w, hw, hc⟩ := nonempty_inter_closedPoints
      (show Wᶜ.Nonempty from ⟨z, hz⟩) hW.isClosed_compl.isLocallyClosed
    exact hw (hcp hc)
  exact Set.mem_iUnion.mp hz

/-- A nonempty source-open patch with open images makes an orbit morphism open
on the entire scheme-point space. -/
public theorem orbitMorphismAt_isOpenMap_of_open_patch
    (U : Set (ofAffine G).toScheme) (hU : IsOpen U) (hne : U.Nonempty)
    (hpatch : ∀ V, IsOpen V → V ⊆ U →
      IsOpen ((A.orbitMorphismAt x).hom '' V)) :
    IsOpenMap (A.orbitMorphismAt x).hom := by
  apply isOpenMap_of_translates (A.orbitMorphismAt x).hom
    (fun g => Scheme.homeoOfIso (leftTranslationIso g))
    (fun g => Scheme.homeoOfIso (A.translationIso g))
    (fun g z => ?_) U hU (translates_cover U hU hne) hpatch
  exact (congrArg (fun f : (ofAffine G).toScheme ⟶ X.toScheme => f z)
    (congrArg Morphism.hom (A.translationMorphism_comp_orbitMorphismAt x g))).symm

/-- Flatness on any nonempty source-open subscheme suffices for openness of the
whole orbit map. This allows inseparable orbit maps. -/
public theorem orbitMorphismAt_isOpenMap_of_flat_patch
    (U : (ofAffine G).toScheme.Opens) (hne : (U : Set (ofAffine G).toScheme).Nonempty)
    (hflat : Flat (U.ι ≫ (A.orbitMorphismAt x).hom)) :
    IsOpenMap (A.orbitMorphismAt x).hom := by
  let f := A.orbitMorphismAt x
  letI : Flat (U.ι ≫ f.hom) := hflat
  letI : LocallyOfFiniteType f.hom := by
    haveI : LocallyOfFiniteType (f.hom ≫ X.structureMap) := by
      rw [f.commutes]
      infer_instance
    exact locallyOfFiniteType_of_comp f.hom X.structureMap
  letI : IsLocallyNoetherian X.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian X.structureMap
  have ho : IsOpenMap (U.ι ≫ f.hom) := (U.ι ≫ f.hom).isOpenMap
  apply A.orbitMorphismAt_isOpenMap_of_open_patch x (U : Set (ofAffine G).toScheme) U.isOpen hne
  intro V hV hVU
  have him : (U.ι ≫ f.hom) '' (U.ι ⁻¹' V) = f.hom '' V := by
    change (f.hom ∘ U.ι) '' (U.ι ⁻¹' V) = _
    rw [Set.image_comp, Set.image_preimage_eq_inter_range,
      Scheme.Opens.range_ι, Set.inter_eq_left.mpr hVU]
  rw [← him]
  exact ho _ (hV.preimage U.ι.continuous)

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
