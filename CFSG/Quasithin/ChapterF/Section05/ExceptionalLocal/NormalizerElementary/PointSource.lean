module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.PlaneMarking
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.PointMatrix

/-!
# The literal joint root and short-root centralizer

The binary point-matrix calculation places the short-root centralizer in
the upper subgroup. The doubled matrix-to-projective equivalence retains the
short root, and the faithful completion transports the containment to the
original T. Thus C_M₁(t)=C_T(t); C_G(z)=M₁ gives C_G(z,t)=C_T(t).

Source: Aschbacher–Smith F.5.5, printed p.301, first paragraph of proof.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Matrix BenderSuzuki.MatrixGroups Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourShortRoot UnitaryFourSylow
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "s" => unipotentSU F σ hσ (shortParameter F σ)

private def pointShortMatrix : UnitaryFourOuter.point F σ hσ :=
  ⟨SemidirectProduct.inl s,UnitaryTwo.ShortRootQuotient.short_mem_point⟩

private theorem short_matrix_fixed : UnitaryFourOuter.matrixAut F σ hσ s=s := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change σ ((unipotentMatrix F (shortParameter F σ).val) i j)=
    (unipotentMatrix F (shortParameter F σ).val) i j
  fin_cases i <;> fin_cases j <;> simp [unipotentMatrix,shortParameter]

private theorem point_matrix_short_centralizer (a : UnitaryFourOuter.point F σ hσ)
    (ha : a*pointShortMatrix=pointShortMatrix*a) :
    a.val∈UnitaryFourOuter.extendedUpper F σ hσ := by
  have hfix : UnitaryFourOuter.action F σ hσ a.val.right s=s := by
    rcases UnitaryFourOuter.c2_cases a.val.right with he | he
    · rw [he,map_one];rfl
    · rw [he,UnitaryFourOuter.action_generator,short_matrix_fixed]
  have hc := congrArg (fun b : UnitaryFourOuter.point F σ hσ => b.val.left) ha
  change a.val.left * UnitaryFourOuter.action F σ hσ a.val.right s =
    s * UnitaryFourOuter.action F σ hσ 1 a.val.left at hc
  rw [hfix,map_one,MulAut.one_apply] at hc
  exact point_centralizer_short_le_upper a.val.left a.property hc

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

private theorem point_short_image :
    endpointMap c i false (Extension.binaryPointMatrixEquiv pointShortMatrix) =
      sourceMarkedShort c i := by
  let a : Extension.overlap 1 hn :=
    ⟨(Extension.binaryPointMatrixEquiv pointShortMatrix).val,by
      rw [←Extension.exact_overlap]
      refine ⟨(Extension.binaryPointMatrixEquiv pointShortMatrix).property,?_⟩
      exact (Extension.mem_plane 1 hn _).mpr (planeParameterMap
        (Multiplicative.ofAdd (shortParameter F σ))).property⟩
  exact congrArg i (DFunLike.congr_fun c.compatible a)

/-- The point-endpoint centralizer of the literal marked short involution
is already contained in the actual source Sylow subgroup. -/
theorem source_point_short_centralizer_le_T (hi : Function.Injective i) :
    M c i false ⊓ centralizer ({sourceMarkedShort c i} : Set G) ≤ Source.sylowImage c i := by
  rintro x ⟨⟨p,rfl⟩,hx⟩
  let a := Extension.binaryPointMatrixEquiv.symm p
  have he : endpointMap c i false (Extension.binaryPointMatrixEquiv a) = endpointMap c i false p :=
    congrArg (endpointMap c i false) (Extension.binaryPointMatrixEquiv.apply_symm_apply p)
  have hc : a*pointShortMatrix=pointShortMatrix*a := by
    apply Extension.binaryPointMatrixEquiv.injective
    apply endpointMap_injective c i hi false
    simpa only [map_mul,point_short_image c i,he] using mem_centralizer_singleton_iff.mp hx
  have hupper : p.val∈Extension.extendedUpper 1 hn := by
    rw [←Extension.binaryPointMatrixEquiv.apply_symm_apply p]
    exact ⟨a.val,point_matrix_short_centralizer a hc,rfl⟩
  rw [source_sylowImage_eq_pointSylow]
  exact ⟨p,hupper,rfl⟩

variable [Finite G] (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (t : G) (hf : FusionFacts c i z t)
include h hf in
/-- The exact point centralizer and hence the joint root/short centralizer. -/
theorem normalizer_point_short_centralizer :
    M c i false ⊓ centralizer ({t} : Set G)=Tcentralizer c i t := by
  apply le_antisymm
  · intro x hx
    refine ⟨?_,hx.2⟩
    rw [fusion_t_eq_marked_short c i z h t hf] at hx
    exact source_point_short_centralizer_le_T c i h.embedding_injective hx
  · exact inf_le_inf (sylowImage_le_M c i false) le_rfl

include h hf in
theorem normalizer_root_short_centralizer :
    centralizer ({rootElement c i z} : Set G) ⊓ centralizer ({t} : Set G)=Tcentralizer c i t := by
  rw [hf.root_centralizer,normalizer_point_short_centralizer c i z h t hf]

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
