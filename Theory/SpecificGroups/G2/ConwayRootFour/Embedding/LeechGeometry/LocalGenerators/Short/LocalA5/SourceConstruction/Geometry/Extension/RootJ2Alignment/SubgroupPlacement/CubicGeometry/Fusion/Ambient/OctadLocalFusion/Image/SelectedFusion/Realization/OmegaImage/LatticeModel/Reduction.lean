/-
Copyright (c) 2026 Gerald Höhn.
The quotient-action construction is adapted from
Atlas/Lattices/LeechModTwo.lean and Atlas/Lattices/LeechModTwoAction.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.ProjectiveLattice

/-!
# Binary reduction of the integral octad lattice

The negative eigensublattice is saturated in the Leech lattice: a vector whose
double is supported on the marked octad is itself supported there. Consequently
its quotient by twice itself embeds in the Leech lattice modulo two. Restriction
of the actual integral centralizer descends to this quotient, and both the
pointwise restriction kernel and the marked scalar sign act trivially.

Split coordinates for the reduced norm transport this particular action to the
binary orthogonal group. Existence of those coordinates, faithfulness modulo
the scalar sign, and identification of the image are separate geometric
obligations; none is assumed in the construction of the quotient action.

Source: Aschbacher, *Sporadic Groups* (1994), 25.2 and 25.4–25.5,
pp.133–134.
-/

@[expose] public noncomputable section
open Atlas.Codes Atlas.Lattices
open Theory.AlgebraicGroup

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage.LatticeModel

def doubleLattice : lattice →+ lattice where
  toFun x := (2 : ℕ) • x
  map_zero' := by simp
  map_add' x y := nsmul_add x y 2

def twiceLattice : AddSubgroup lattice := doubleLattice.range

/-- Reduction in the lattice itself, not coordinatewise reduction modulo two. -/
abbrev ModTwo := lattice ⧸ twiceLattice

def reduction : lattice →+ ModTwo := QuotientAddGroup.mk' twiceLattice

theorem reduction_surjective : Function.Surjective reduction :=
  QuotientAddGroup.mk'_surjective _

theorem reduction_eq_zero (x : lattice) :
    reduction x = 0 ↔ ∃ y : lattice, (2 : ℕ) • y = x := by
  exact QuotientAddGroup.eq_zero_iff x

instance : Module (ZMod 2) ModTwo := QuotientAddGroup.zmodModule (n := 2)
  (fun x => ⟨x, rfl⟩ : ∀ x : lattice, (2 : ℕ) • x ∈ twiceLattice)

/-- Saturation of the supported sublattice under division by two. -/
theorem mem_lattice_of_double_mem (x : leech) (hx : (2 : ℕ) • x ∈ lattice) :
    x ∈ lattice := by
  rw [mem_lattice_iff_support] at hx ⊢
  intro i hi
  have h := hx i hi
  change (2 : ℤ) * x.val i = 0 at h
  omega

def leechInclusion : ModTwo →+ LeechModTwo :=
  QuotientAddGroup.lift twiceLattice
    (leechReduction.comp lattice.subtype.toAddMonoidHom) (by
      rintro x ⟨y, rfl⟩
      exact (leechReduction_eq_zero _).mpr ⟨y.val, rfl⟩)

theorem leechInclusion_reduction (x : lattice) :
    leechInclusion (reduction x) = leechReduction x.val := rfl

/-- The source's octad binary space is a genuine subspace of Leech modulo two. -/
theorem leechInclusion_injective : Function.Injective leechInclusion := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro a ha
  obtain ⟨x, rfl⟩ := reduction_surjective a
  obtain ⟨y, hy⟩ := (leechReduction_eq_zero x.val).mp ha
  have hyl : y ∈ lattice := mem_lattice_of_double_mem y (hy.symm ▸ x.prop)
  exact (reduction_eq_zero x).mpr ⟨⟨y, hyl⟩, Subtype.ext hy⟩

instance : Finite ModTwo := Finite.of_injective leechInclusion leechInclusion_injective

def actionMap (g : centralizer) : ModTwo →+ ModTwo :=
  QuotientAddGroup.lift twiceLattice
    (reduction.comp (action g).toAddEquiv.toAddMonoidHom) (by
      rintro x ⟨y, rfl⟩
      change reduction (action g ((2 : ℕ) • y)) = 0
      rw [map_nsmul]
      exact (reduction_eq_zero _).mpr ⟨action g y, rfl⟩)

theorem actionMap_reduction (g : centralizer) (x : lattice) :
    actionMap g (reduction x) = reduction (action g x) := rfl

theorem actionMap_one (a : ModTwo) : actionMap 1 a = a := by
  obtain ⟨x, rfl⟩ := reduction_surjective a
  change reduction (action 1 x) = reduction x
  rw [map_one]
  rfl

theorem actionMap_mul (g h : centralizer) (a : ModTwo) :
    actionMap (g * h) a = actionMap g (actionMap h a) := by
  obtain ⟨x, rfl⟩ := reduction_surjective a
  change reduction (action (g * h) x) = reduction (action g (action h x))
  rw [map_mul]
  rfl

def linearAction : centralizer →* (ModTwo ≃ₗ[ZMod 2] ModTwo) where
  toFun g :=
    { toFun := actionMap g
      invFun := actionMap g⁻¹
      left_inv := by intro a; rw [← actionMap_mul, inv_mul_cancel, actionMap_one]
      right_inv := by intro a; rw [← actionMap_mul, mul_inv_cancel, actionMap_one]
      map_add' := (actionMap g).map_add
      map_smul' := ZMod.map_smul (actionMap g) }
  map_one' := by ext a; exact actionMap_one a
  map_mul' g h := by ext a; exact actionMap_mul g h a

theorem linearAction_reduction (g : centralizer) (x : lattice) :
    linearAction g (reduction x) = reduction (action g x) := rfl

/-- Compatibility with the full Leech action uses the literal lattice inclusion. -/
theorem leechInclusion_equivariant (g : centralizer) (a : ModTwo) :
    leechInclusion (linearAction g a) =
      leechModTwoRepresentation g.val (leechInclusion a) := by
  obtain ⟨x, rfl⟩ := reduction_surjective a
  rfl

theorem linearAction_kernel_iff (g : centralizer) :
    g ∈ linearAction.ker ↔ ∀ x : lattice,
      ∃ y : lattice, (2 : ℕ) • y = action g x - x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg x
    apply (reduction_eq_zero _).mp
    rw [map_sub, ← linearAction_reduction, hg]
    exact sub_self _
  · intro hg
    apply LinearEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := reduction_surjective a
    change reduction (action g x) = reduction x
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (reduction_eq_zero _).mpr (hg x)

/-- Both parts of the actual projective kernel vanish in binary reduction. -/
theorem projectiveLatticeKernel_le_linearAction_ker :
    projectiveLatticeKernel ≤ linearAction.ker := by
  apply sup_le
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply LinearEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := reduction_surjective a
    rw [linearAction_reduction, hg]
    rfl
  · apply Subgroup.zpowers_le.mpr
    rw [MonoidHom.mem_ker]
    apply LinearEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := reduction_surjective a
    rw [linearAction_reduction, action_octadSign]
    apply leechInclusion_injective
    exact leechReduction_neg x.val

/-- Coordinates for the actual reduced octad norm. No group-image conclusion
is part of this geometric interface. -/
structure Coordinates where
  coordinates : ModTwo ≃ₗ[ZMod 2] SelectedGeometry.Space
  norm (x : lattice) :
    SelectedGeometry.form (coordinates (reduction x)) =
      ((integerDot x.val.val x.val.val / 32 : ℤ) : ZMod 2)

namespace Coordinates
variable (C : Coordinates)

def linearAction : centralizer →*
    (SelectedGeometry.Space ≃ₗ[ZMod 2] SelectedGeometry.Space) where
  toFun g := (C.coordinates.symm.trans (LatticeModel.linearAction g)).trans C.coordinates
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change C.coordinates (LatticeModel.linearAction 1 (C.coordinates.symm v)) = v
    rw [map_one]
    exact C.coordinates.apply_symm_apply v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change C.coordinates (LatticeModel.linearAction (g * h) (C.coordinates.symm v)) =
      C.coordinates (LatticeModel.linearAction g
        (C.coordinates.symm (C.coordinates (LatticeModel.linearAction h (C.coordinates.symm v)))))
    rw [LinearEquiv.symm_apply_apply, map_mul]
    rfl

theorem linearAction_reduction (g : centralizer) (x : lattice) :
    C.linearAction g (C.coordinates (reduction x)) =
      C.coordinates (reduction (action g x)) := by
  change C.coordinates (LatticeModel.linearAction g
    (C.coordinates.symm (C.coordinates (reduction x)))) = _
  rw [LinearEquiv.symm_apply_apply, LatticeModel.linearAction_reduction]

theorem linearAction_preserves_form (g : centralizer) (v : SelectedGeometry.Space) :
    SelectedGeometry.form (C.linearAction g v) = SelectedGeometry.form v := by
  obtain ⟨a, rfl⟩ := C.coordinates.surjective v
  obtain ⟨x, rfl⟩ := reduction_surjective a
  rw [C.linearAction_reduction, C.norm, C.norm, action_preserves_form]

def orthogonalAction : centralizer →* SelectedGeometry.Orthogonal :=
  C.linearAction.codRestrict (quadraticIsometrySubgroup SelectedGeometry.form)
    (fun g => (mem_quadraticIsometrySubgroup _ _).mpr (C.linearAction_preserves_form g))

theorem orthogonalAction_reduction (g : centralizer) (x : lattice) :
    (C.orthogonalAction g).val (C.coordinates (reduction x)) =
      C.coordinates (reduction (action g x)) := C.linearAction_reduction g x

theorem orthogonalAction_ker :
    C.orthogonalAction.ker = LatticeModel.linearAction.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hg
    apply LinearEquiv.ext
    intro a
    have h := congrArg (fun f : SelectedGeometry.Orthogonal => f.val (C.coordinates a)) hg
    change C.coordinates (LatticeModel.linearAction g
      (C.coordinates.symm (C.coordinates a))) = C.coordinates a at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact C.coordinates.injective h
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change C.coordinates (LatticeModel.linearAction g (C.coordinates.symm v)) = v
    rw [hg]
    exact C.coordinates.apply_symm_apply v

/-- The binary lattice representation factors through the published projective
integral image, without identifying it with the full lattice isometry group. -/
def projectiveAction : ProjectiveLatticeImage →* SelectedGeometry.Orthogonal :=
  QuotientGroup.lift projectiveLatticeKernel C.orthogonalAction (by
    rw [C.orthogonalAction_ker]
    exact projectiveLatticeKernel_le_linearAction_ker)

theorem projectiveAction_mk (g : centralizer) :
    C.projectiveAction (projectiveLatticeMap g) = C.orthogonalAction g := rfl

/-- Final quotient assembly once the two independent geometric calculations
(kernel and image) have been proved. -/
def projectiveEquiv
    (hKernel : LatticeModel.linearAction.ker = projectiveLatticeKernel)
    (hImage : C.orthogonalAction.range = SelectedGeometry.omega) :
    ProjectiveLatticeImage ≃* SelectedGeometry.omega :=
  (QuotientGroup.quotientMulEquivOfEq
    (C.orthogonalAction_ker.trans hKernel).symm).trans
      ((QuotientGroup.quotientKerEquivRange C.orthogonalAction).trans
        (MulEquiv.subgroupCongr hImage))

theorem projectiveEquiv_mk
    (hKernel : LatticeModel.linearAction.ker = projectiveLatticeKernel)
    (hImage : C.orthogonalAction.range = SelectedGeometry.omega) (g : centralizer) :
    (C.projectiveEquiv hKernel hImage (projectiveLatticeMap g)).val =
      C.orthogonalAction g := rfl

end Coordinates
end Realization.OmegaImage.LatticeModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
