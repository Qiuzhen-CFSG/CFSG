module

public import Theory.SpecificGroups.ClassicalOrthogonal.D3ExteriorComparison.GeneralTransport
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.Standard
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Elementary
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.ScalarKernel
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Split-six exterior comparison over any odd field

The exterior-square representation lands in the elementary orthogonal group
because SL₄ is perfect and the full isometry quotient is abelian. Its exact
scalar kernel induces the projective comparison. Explicit singular-vector
transport and the Siegel generators prove surjectivity, without an order
formula or a simplicity premise.

Source: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.D3ExteriorComparison.General
open Theory.AlgebraicGroup
open ClassicalOrthogonal ClassicalOrthogonal.Quadratic
open ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Fundamental.SplitOddBlocks
open Atlas.Order20160A8.Exterior
open Matrix

variable {F : Type} [Field F]

theorem elementary_eq_commutator (h2 : (2 : F) ≠ 0) : elementarySubgroup (formD 3 F) = commutator (quadraticIsometrySubgroup (formD 3 F)) := by
  apply le_antisymm
  · exact elementary_le_commutator_odd (formD 3 F) polarD_nondegenerate (by rw [Module.finrank_pi]; decide) h2
  · let _ := elementary_normal (formD 3 F)
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (ClassicalOrthogonal.Fundamental.SplitOddBlocks.IsometryQuotients.elementaryQuotient_isMulCommutative
        (formD 3 F) (wittTwoFrameD 1) polarD_nondegenerate h2)

theorem toOrthogonal_mem_elementary (h2 : (2 : F) ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    toOrthogonal g ∈ elementarySubgroup (formD 3 F) := by
  let _ := Atlas.sl_perfect (F := F) 4 (by decide)
  let _ := Group.IsPerfect.range (toOrthogonal (F := F))
  have hr : toOrthogonal g ∈ (toOrthogonal (F := F)).range := ⟨g,rfl⟩
  rw [← Subgroup.commutator_eq_self (H := (toOrthogonal (F := F)).range)] at hr
  have hc : toOrthogonal g ∈ commutator (quadraticIsometrySubgroup (formD 3 F)) :=
    Subgroup.commutator_mono le_top le_top hr
  exact elementary_eq_commutator h2 ▸ hc

def toElementary (h2 : (2 : F) ≠ 0) : Matrix.SpecialLinearGroup (Fin 4) F →* elementarySubgroup (formD 3 F) :=
  (toOrthogonal (F := F)).codRestrict _ (toOrthogonal_mem_elementary h2)

namespace Kernel
open Atlas.Order20160A8.Bivectors
 theorem toOrthogonal_scalar_iff (g : Matrix.SpecialLinearGroup (Fin 4) F) (c : F) :
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

 theorem toOrthogonal_eq_one_iff (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    toOrthogonal g = 1 ↔ ∃ a : F, a^2 = 1 ∧ g.val = a • 1 := by
  constructor
  · intro hg
    apply Atlas.Order20160A8.Bivectors.scalar_of_exteriorMap_eq_id
    have hs : ∀ v, (toOrthogonal g).val v = (1 : F) • v := by
      rw [hg]
      intro v
      exact (one_smul F v).symm
    simpa only [one_smul] using (toOrthogonal_scalar_iff g 1).mp hs
  · rintro ⟨a,ha,hg⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates (exteriorMap g.val (coordinates.symm v)) = v
    rw [hg, ClassicalOrthogonal.Minus.OddSixComparison.exteriorMap_scalar, ha, one_smul,
      LinearMap.id_apply, LinearEquiv.apply_symm_apply]

end Kernel

def toProjective (h2 : (2 : F) ≠ 0) : Matrix.SpecialLinearGroup (Fin 4) F →* ClassicalOrthogonal.POmegaPlus 3 F :=
  (projectiveElementaryMap (formD 3 F)).comp (toElementary h2)

theorem toProjective_eq_one_iff_center (h2 : (2 : F) ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    toProjective h2 g = 1 ↔ g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F) := by
  change (QuotientGroup.mk (toElementary h2 g) : ClassicalOrthogonal.POmegaPlus 3 F) = 1 ↔ _
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
    have hm : g.val = a • (1 : Matrix (Fin 4) (Fin 4) F) := by
      simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using hga.symm
    refine ⟨a^2, ?_, ?_⟩
    · norm_num only [Fintype.card_fin] at ha
      simpa only [← pow_mul] using ha
    · apply (Kernel.toOrthogonal_scalar_iff g (a^2)).mpr
      intro w
      rw [hm, ClassicalOrthogonal.Minus.OddSixComparison.exteriorMap_scalar, LinearMap.smul_apply,
        LinearMap.id_apply]

theorem toProjective_kernel (h2 : (2 : F) ≠ 0) :
    (toProjective h2).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F) := by
  ext g
  exact toProjective_eq_one_iff_center h2 g

def projectiveHom (h2 : (2 : F) ≠ 0) : Matrix.ProjectiveSpecialLinearGroup (Fin 4) F →*
    ClassicalOrthogonal.POmegaPlus 3 F :=
  QuotientGroup.lift _ (toProjective h2) (by
    intro g hg
    exact (toProjective_eq_one_iff_center h2 g).mpr hg)

theorem projectiveHom_projection (h2 : (2 : F) ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    projectiveHom h2 (QuotientGroup.mk g) = projectiveElementaryMap (formD 3 F) (toElementary h2 g) := rfl

theorem projectiveHom_injective (h2 : (2 : F) ≠ 0) : Function.Injective (projectiveHom h2) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F)) x
  change projectiveHom h2 (QuotientGroup.mk g) = 1 at hx
  change QuotientGroup.mk g = (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 4) F)
  apply (QuotientGroup.eq_one_iff g).mpr
  exact (toProjective_eq_one_iff_center h2 g).mp hx


/-- Every elementary split-six isometry is an exterior square. -/
theorem toElementary_surjective (h2 : (2 : F) ≠ 0) :
    Function.Surjective (toElementary h2) := by
  have hle : elementarySubgroup (formD 3 F) ≤ (toOrthogonal (F := F)).range := by
    apply elementary_le_of_siegel_and_transport (formD 3 F) _ (e 0) (formD_e 0)
    · intro v hv
      exact ⟨GeneralTransport.upper v, GeneralTransport.upper_action v hv⟩
    · intro u hu hq
      obtain ⟨a, ha⟩ := GeneralTransport.singular_transport u hu hq
      exact ⟨toOrthogonal a, ⟨a, rfl⟩, ha⟩
  intro g
  obtain ⟨a, ha⟩ := hle g.prop
  exact ⟨a, Subtype.ext ha⟩

theorem projectiveHom_surjective (h2 : (2 : F) ≠ 0) :
    Function.Surjective (projectiveHom h2) := by
  intro x
  obtain ⟨g, rfl⟩ := projectiveElementaryMap_surjective (formD 3 F) x
  obtain ⟨a, rfl⟩ := toElementary_surjective h2 g
  exact ⟨QuotientGroup.mk a, projectiveHom_projection h2 a⟩

/-- The field-preserving exceptional isomorphism D₃ = A₃. -/
def projectiveEquiv (h2 : (2 : F) ≠ 0) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 4) F ≃* POmegaPlus 3 F :=
  MulEquiv.ofBijective (projectiveHom h2)
    ⟨projectiveHom_injective h2, projectiveHom_surjective h2⟩

@[simp] theorem projectiveEquiv_projection (h2 : (2 : F) ≠ 0)
    (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    projectiveEquiv h2 (QuotientGroup.mk g) =
      projectiveElementaryMap (formD 3 F) (toElementary h2 g) := rfl

end ClassicalOrthogonal.D3ExteriorComparison.General
