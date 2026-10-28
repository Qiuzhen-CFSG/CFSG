/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianCentralizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianScalarIsometries

/-!
# IcosianCentralizer

The full right-quaternion-linear Hermitian lattice group is isomorphic to the scalar
centralizer in the Leech isometry group. The lattice isometry transports both
directions.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianCentralizer.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.LinearAlgebra

/-- The full right-D-linear Hermitian isometry group of the actual integral lattice. -/
def icosianHermitianGroup :
    Subgroup (IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates) where
  carrier := {f | (∀ a x,f (icosianRightMul x a)=icosianRightMul (f x) a) ∧
    (∀ x y,icosianHermitian (f x) (f y)=icosianHermitian x y) ∧
    ∀ x,x ∈ rationalIcosianLattice ↔ f x ∈ rationalIcosianLattice}
  one_mem' := ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro f g ⟨hf,hH,hL⟩ ⟨hg,kH,kL⟩
    refine ⟨fun a x => ?_,fun x y => ?_,fun x => ?_⟩
    · change f (g (icosianRightMul x a))=icosianRightMul (f (g x)) a
      rw [hg,hf]
    · change icosianHermitian (f (g x)) (f (g y))=_
      rw [hH,kH]
    · exact (kL x).trans (hL (g x))
  inv_mem' := by
    rintro f ⟨hf,hH,hL⟩
    refine ⟨fun a x => ?_,fun x y => ?_,fun x => ?_⟩
    · change f.symm (icosianRightMul x a)=icosianRightMul (f.symm x) a
      apply f.injective
      rw [f.apply_symm_apply,hf,f.apply_symm_apply]
    · have h := hH (f.symm x) (f.symm y)
      change icosianHermitian (f.symm x) (f.symm y)=_
      simpa only [LinearEquiv.apply_symm_apply,icosianBilinear] using h.symm
    · have h := hL (f.symm x)
      change x ∈ rationalIcosianLattice ↔ f.symm x ∈ rationalIcosianLattice
      simpa only [LinearEquiv.apply_symm_apply,icosianBilinear] using h.symm

/-- Equality of full conditions: no proper subgroup is substituted for the
linear Hermitian lattice stabilizer or for the scalar centralizer. -/
theorem icosianHermitianGroup_iff
    (f : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates) :
    f ∈ icosianHermitianGroup ↔
      icosianAutomorphismComparison f ∈ rationalLatticeIsometries ∧
      ∀ u,icosianAutomorphismComparison f*icosianRationalScalar u=
        icosianRationalScalar u*icosianAutomorphismComparison f := by
  have hc : (∀ u,icosianAutomorphismComparison f*icosianRationalScalar u=
      icosianRationalScalar u*icosianAutomorphismComparison f) ↔
      ∀ a x,f (icosianRightMul x a)=icosianRightMul (f x) a := by
    simp only [icosianRationalScalar,← map_mul,icosianAutomorphismComparison.injective.eq_iff]
    exact (icosian_right_linear_iff_scalar_commutation f).symm
  constructor
  · rintro ⟨hl,hH,hL⟩
    refine ⟨⟨fun x y => ?_,fun x => ?_⟩,hc.mpr hl⟩
    · change rationalForm (icosianComparison (f (icosianComparison.symm x)))
        (icosianComparison (f (icosianComparison.symm y)))=_
      rw [icosianComparison_isometry]
      unfold icosianBilinear
      rw [hH]
      have h := icosianComparison_isometry (icosianComparison.symm x) (icosianComparison.symm y)
      simpa only [LinearEquiv.apply_symm_apply,icosianBilinear] using h.symm
    · have h := (icosianComparison_lattice_iff (icosianComparison.symm x)).symm.trans
        ((hL (icosianComparison.symm x)).trans
          (icosianComparison_lattice_iff (f (icosianComparison.symm x))))
      change x ∈ rationalLeech ↔ icosianComparison (f (icosianComparison.symm x)) ∈ rationalLeech
      simpa only [LinearEquiv.apply_symm_apply] using h
  · rintro ⟨⟨hB,hL⟩,hcomm⟩
    have hl := hc.mp hcomm
    have hf : ∀ x y,icosianBilinear (f x) (f y)=icosianBilinear x y := by
      intro x y
      have h := hB (icosianComparison x) (icosianComparison y)
      change rationalForm
        (icosianComparison (f (icosianComparison.symm (icosianComparison x))))
        (icosianComparison (f (icosianComparison.symm (icosianComparison y))))=_ at h
      simpa only [LinearEquiv.symm_apply_apply,icosianComparison_isometry] using h
    refine ⟨hl,icosianHermitian_of_bilinear_and_right_linear f hf hl,fun x => ?_⟩
    have h := (icosianComparison_lattice_iff x).trans (hL (icosianComparison x))
    change x ∈ rationalIcosianLattice ↔
      icosianComparison (f (icosianComparison.symm (icosianComparison x))) ∈ rationalLeech at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h.trans (icosianComparison_lattice_iff (f x)).symm

def icosianHermitianToRational : icosianHermitianGroup →* rationalLatticeIsometries where
  toFun f := ⟨icosianAutomorphismComparison f.val,(icosianHermitianGroup_iff f.val).mp f.property |>.1⟩
  map_one' := by apply Subtype.ext; exact map_one icosianAutomorphismComparison
  map_mul' f g := by apply Subtype.ext; exact map_mul icosianAutomorphismComparison f.val g.val

def icosianHermitianToCo0 : icosianHermitianGroup →* LeechIsometryGroup :=
  fullIsometryEquiv.symm.toMonoidHom.comp icosianHermitianToRational

theorem icosianHermitianToCo0_extension (f : icosianHermitianGroup) :
    fullIsometryEquiv (icosianHermitianToCo0 f)=icosianHermitianToRational f :=
  fullIsometryEquiv.apply_symm_apply _

theorem icosianHermitianToCo0_injective : Function.Injective icosianHermitianToCo0 := by
  intro f g h
  apply Subtype.ext
  apply icosianAutomorphismComparison.injective
  have hr := congrArg (fun k : LeechIsometryGroup => (fullIsometryEquiv k).val) h
  rw [icosianHermitianToCo0_extension,icosianHermitianToCo0_extension] at hr
  exact hr

theorem icosianHermitianToCo0_mem (f : icosianHermitianGroup) :
    icosianHermitianToCo0 f ∈ icosianCentralizer := by
  apply (icosianCentralizer_mem _).mpr
  intro u
  apply fullIsometryEquiv.injective
  rw [map_mul,map_mul,icosianScalarsToCo0_extension,icosianHermitianToCo0_extension]
  apply Subtype.ext
  exact (icosianHermitianGroup_iff f.val).mp f.property |>.2 u

theorem icosianHermitianToCo0_surjective_centralizer
    (g : icosianCentralizer) : ∃ f,icosianHermitianToCo0 f=g.val := by
  let r := fullIsometryEquiv g.val
  let f := icosianAutomorphismComparison.symm r.val
  have hf : f ∈ icosianHermitianGroup := by
    apply (icosianHermitianGroup_iff f).mpr
    have he : icosianAutomorphismComparison f=r.val :=
      icosianAutomorphismComparison.apply_symm_apply _
    rw [he]
    refine ⟨r.property,fun u => ?_⟩
    have h := congrArg fullIsometryEquiv ((icosianCentralizer_mem g.val).mp g.property u)
    rw [map_mul,map_mul,icosianScalarsToCo0_extension] at h
    exact congrArg Subtype.val h
  refine ⟨⟨f,hf⟩,?_⟩
  apply fullIsometryEquiv.injective
  rw [icosianHermitianToCo0_extension]
  apply Subtype.ext
  exact icosianAutomorphismComparison.apply_symm_apply r.val

theorem icosianHermitianToCo0_range : icosianHermitianToCo0.range=icosianCentralizer := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨f,rfl⟩; exact icosianHermitianToCo0_mem f
  · intro hg
    obtain ⟨f,hf⟩ := icosianHermitianToCo0_surjective_centralizer ⟨g,hg⟩
    exact ⟨f,hf⟩

/-- The full Hermitian lattice group is exactly the actual right-scalar centralizer in Co0. -/
def icosianCentralizerEquiv : icosianHermitianGroup ≃* icosianCentralizer :=
  (MonoidHom.ofInjective icosianHermitianToCo0_injective).trans
    (MulEquiv.subgroupCongr icosianHermitianToCo0_range)

end Atlas.Conway
