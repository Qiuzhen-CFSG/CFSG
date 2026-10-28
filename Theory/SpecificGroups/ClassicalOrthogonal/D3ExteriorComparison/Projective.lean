module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorOrthogonal
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.Standard
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Elementary
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.ScalarKernel
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The ternary split-D3 exterior-square comparison

The Pfaffian coordinates in the existing Atlas port turn the exterior square of
`SL(4, 3)` into the literal split six-dimensional quadratic model.  This file
proves the image containment using the repository's odd-characteristic
commutator quotient, then proves the exact scalar kernel and the induced
injective map from `PSL(4, 3)` to the projective Omega carrier.  The final
surjectivity/equivalence theorem is parameterized by the separately proved
finite-order equality; this keeps the order calculation at its mathematical
source boundary.

Source: Atlas `D3ExteriorImage`, `D3ExteriorKernel`, and
`D3ExteriorProjective`; GLS3 §2.7 and Aschbacher--Smith A.2.17.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.D3ExteriorComparison
open Theory.AlgebraicGroup
open ClassicalOrthogonal ClassicalOrthogonal.Quadratic
open ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Fundamental.SplitOddBlocks
open Atlas.Order20160A8.Exterior
open Matrix

abbrev Q : QuadraticForm (ZMod 3) (ClassicalOrthogonal.VectorD 3 (ZMod 3)) := formD 3 (ZMod 3)
theorem elementary_eq_commutator : elementarySubgroup Q = commutator (quadraticIsometrySubgroup Q) := by
  apply le_antisymm
  · exact elementary_le_commutator_odd Q polarD_nondegenerate (by rw [Module.finrank_pi]; decide) (by decide)
  · let _ := elementary_normal Q
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (ClassicalOrthogonal.Fundamental.SplitOddBlocks.IsometryQuotients.elementaryQuotient_isMulCommutative
        Q (wittTwoFrameD 1) polarD_nondegenerate (by decide))

theorem toOrthogonal_mem_elementary (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) :
    toOrthogonal g ∈ elementarySubgroup Q := by
  let _ := Atlas.sl_perfect (F := ZMod 3) 4 (by decide)
  let _ := Group.IsPerfect.range (toOrthogonal (F := ZMod 3))
  have hr : toOrthogonal g ∈ (toOrthogonal (F := ZMod 3)).range := ⟨g,rfl⟩
  rw [← Subgroup.commutator_eq_self (H := (toOrthogonal (F := ZMod 3)).range)] at hr
  have hc : toOrthogonal g ∈ commutator (quadraticIsometrySubgroup Q) :=
    Subgroup.commutator_mono le_top le_top hr
  exact elementary_eq_commutator ▸ hc

def toElementary : Matrix.SpecialLinearGroup (Fin 4) (ZMod 3) →* elementarySubgroup Q :=
  (toOrthogonal (F := ZMod 3)).codRestrict _ toOrthogonal_mem_elementary

namespace Kernel
open Atlas.Order20160A8.Bivectors
 theorem toOrthogonal_scalar_iff (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) (c : ZMod 3) :
    (∀ v, (toOrthogonal g).val v = c • v) ↔
      (∀ w, exteriorMap g.val w = c • w) := by
  constructor
  · intro h w
    apply coordinates.injective
    have hv := h (coordinates w)
    change coordinates (exteriorMap g.val (coordinates.symm (coordinates w))) = c • coordinates w at hv
    simpa only [LinearEquiv.symm_apply_apply, map_smul] using hv
  · intro h v
    change coordinates (exteriorMap g.val (coordinates.symm v)) = c • v
    rw [h, map_smul, LinearEquiv.apply_symm_apply]

 theorem toOrthogonal_eq_one_iff (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) :
    toOrthogonal g = 1 ↔ ∃ a : ZMod 3, a^2 = 1 ∧ g.val = a • 1 := by
  constructor
  · intro hg
    apply Atlas.Order20160A8.Bivectors.scalar_of_exteriorMap_eq_id
    have hs : ∀ v, (toOrthogonal g).val v = (1 : ZMod 3) • v := by
      rw [hg]
      intro v
      exact (one_smul (ZMod 3) v).symm
    simpa only [one_smul] using (toOrthogonal_scalar_iff g 1).mp hs
  · rintro ⟨a,ha,hg⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates (exteriorMap g.val (coordinates.symm v)) = v
    rw [hg, ClassicalOrthogonal.Minus.OddSixComparison.exteriorMap_scalar, ha, one_smul,
      LinearMap.id_apply, LinearEquiv.apply_symm_apply]

end Kernel

def toProjective : Matrix.SpecialLinearGroup (Fin 4) (ZMod 3) →* ClassicalOrthogonal.POmegaPlus 3 (ZMod 3) :=
  (projectiveElementaryMap Q).comp toElementary

theorem toProjective_eq_one_iff_center (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) :
    toProjective g = 1 ↔ g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) := by
  change (QuotientGroup.mk (toElementary g) : ClassicalOrthogonal.POmegaPlus 3 (ZMod 3)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨c,hc,hg⟩
    have hc0 : c ≠ 0 := by intro hz; simp [hz] at hc
    obtain ⟨a,ha,hga⟩ := ClassicalOrthogonal.Minus.OddSixComparison.scalar_of_exteriorMap_scalar
      g.val c hc0 ((Kernel.toOrthogonal_scalar_iff g c).mp hg)
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨a, ?_, ?_⟩
    · have hd := g.det_coe
      rw [hga, Matrix.det_smul] at hd
      simpa using hd
    · simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using hga.symm
  · intro hg
    obtain ⟨a,ha,hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
    have hm : g.val = a • (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) := by
      simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using hga.symm
    refine ⟨a^2, ?_, ?_⟩
    · norm_num only [Fintype.card_fin] at ha
      simpa only [← pow_mul] using ha
    · apply (Kernel.toOrthogonal_scalar_iff g (a^2)).mpr
      intro w
      rw [hm, ClassicalOrthogonal.Minus.OddSixComparison.exteriorMap_scalar, LinearMap.smul_apply,
        LinearMap.id_apply]

theorem toProjective_kernel :
    (toProjective).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) := by
  ext g
  exact toProjective_eq_one_iff_center g

def projectiveHom : Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3) →*
    ClassicalOrthogonal.POmegaPlus 3 (ZMod 3) :=
  QuotientGroup.lift _ toProjective (by
    intro g hg
    exact (toProjective_eq_one_iff_center g).mpr hg)

theorem projectiveHom_projection (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) :
    projectiveHom (QuotientGroup.mk g) = projectiveElementaryMap Q (toElementary g) := rfl

theorem projectiveHom_injective : Function.Injective projectiveHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3))) x
  change projectiveHom (QuotientGroup.mk g) = 1 at hx
  change QuotientGroup.mk g = (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3))
  apply (QuotientGroup.eq_one_iff g).mpr
  exact (toProjective_eq_one_iff_center g).mp hx

/-- The source projective linear group has order 6065280. -/
theorem psl4_three_card :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) = 6065280 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 3) 4
  norm_num [Fin.prod_univ_succ] at h
  rw [Nat.card_eq_fintype_card]
  have h' : Fintype.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) * 4 = 24261120 := by
    nlinarith [h]
  apply Nat.eq_of_mul_eq_mul_right (m := 4) (by decide)
  calc
    Fintype.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) * 4 = 24261120 := h'
    _ = 6065280 * 4 := by norm_num

/-- Surjectivity follows from the exact finite order of the two carriers. -/
theorem projectiveHom_surjective_of_card
    (hcard : Nat.card (ClassicalOrthogonal.POmegaPlus 3 (ZMod 3)) = 6065280) :
    Function.Surjective projectiveHom := by
  have hb : Function.Bijective projectiveHom :=
    (Nat.bijective_iff_injective_and_card _).mpr
      ⟨projectiveHom_injective, by rw [psl4_three_card, hcard]⟩
  exact hb.surjective

/-- The actual projective D3/PSL4 equivalence, once the order calculation is supplied. -/
def projectiveEquiv_of_card
    (hcard : Nat.card (ClassicalOrthogonal.POmegaPlus 3 (ZMod 3)) = 6065280) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3) ≃*
      ClassicalOrthogonal.POmegaPlus 3 (ZMod 3) :=
  MulEquiv.ofBijective projectiveHom
    (⟨projectiveHom_injective, projectiveHom_surjective_of_card hcard⟩)

@[simp] theorem projectiveEquiv_of_card_projection
    (hcard : Nat.card (ClassicalOrthogonal.POmegaPlus 3 (ZMod 3)) = 6065280)
    (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) :
    projectiveEquiv_of_card hcard (QuotientGroup.mk g) =
      projectiveElementaryMap Q (toElementary g) :=
  projectiveHom_projection g

/-- Simplicity of the projective Omega carrier follows from the comparison. -/
theorem projective_simple_of_card
    (hcard : Nat.card (ClassicalOrthogonal.POmegaPlus 3 (ZMod 3)) = 6065280) :
    IsSimpleGroup (ClassicalOrthogonal.POmegaPlus 3 (ZMod 3)) := by
  let _ := Atlas.psl_simple_high_rank (F := ZMod 3) 4 (by decide)
  exact (projectiveEquiv_of_card hcard).symm.isSimpleGroup

end ClassicalOrthogonal.D3ExteriorComparison
