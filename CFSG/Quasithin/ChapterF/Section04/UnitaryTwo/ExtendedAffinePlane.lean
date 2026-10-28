module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.PlaneAction
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.BinaryOrders
public import Theory.Representation.BinaryAlternatingFiveExtension.OuterRecognition
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.AffinePlane
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ModelClasses

/-!
# The marked affine model of the doubled binary unitary plane

The doubled plane acts faithfully by conjugation on its ordinary plane.
Transport that action through the already marked affine A₅ equivalence.
The faithful-extension theorem and the literal order 1,920 identify the
whole plane with the affine S₅ group while retaining every translation.
Entrywise Frobenius fixes the rational long-root matrix, so the centralizer
of the same lifted root is exactly the extended flag overlap.

Source: Aschbacher--Smith 13.5.17, printed p.922, doubled unitary branch.
All action, order, module, root and centralizer premises are proved for the
literal q-Frobenius extension.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ExtendedAffinePlane
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourShortRoot
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "P" => planeParabolic 1 hn
local notation "PE" => Extension.plane 1 hn

private theorem projectiveAut_longRight :
    Extension.projectiveAut 1 hn ModelClasses.longRight.val = ModelClasses.longRight.val := by
  let z : MatrixGroup 1 hn := (longLocal F σ hσ).val
  change Extension.projectiveAut 1 hn (Extension.projectEquiv 1 hn z) =
    Extension.projectEquiv 1 hn z
  rw [Extension.projectiveAut_project 1 hn z]
  apply congrArg (Extension.projectEquiv 1 hn)
  apply Subtype.ext
  apply Units.ext
  ext i j
  change σ ((unipotentMatrix F (longParameter F σ).val) i j) = (unipotentMatrix F (longParameter F σ).val) i j
  fin_cases i <;> fin_cases j <;> simp [unipotentMatrix,longParameter]

/-- The same long-root element in the literal extended plane. -/
def longRight : PE := ⟨SemidirectProduct.inl ModelClasses.longRight.val,
  (Extension.mem_plane 1 hn _).mpr ModelClasses.longRight.property⟩

/-- The extended flag overlap is the centralizer of this root. -/
theorem right_long_centralizer : centralizer ({longRight} : Set PE) =
    (Extension.overlap 1 hn).subgroupOf PE := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change x * longRight = longRight * x ↔ _
  have hfix : Extension.projectiveAction 1 hn x.val.right ModelClasses.longRight.val =
      ModelClasses.longRight.val := by
    rcases UnitaryFourOuter.c2_cases x.val.right with h | h
    · rw [h,map_one]; rfl
    · rw [h,Extension.projectiveAction_generator,projectiveAut_longRight]
  have he : x * longRight = longRight * x ↔
      x.val.left * ModelClasses.longRight.val = ModelClasses.longRight.val * x.val.left := by
    constructor
    · intro hh
      have hh' := congrArg (fun y : PE => y.val.left) hh
      change x.val.left * Extension.projectiveAction 1 hn x.val.right ModelClasses.longRight.val =
        ModelClasses.longRight.val * Extension.projectiveAction 1 hn 1 x.val.left at hh'
      simpa only [hfix,map_one,MulAut.one_apply] using hh'
    · intro hh
      apply Subtype.ext
      apply SemidirectProduct.ext
      · change x.val.left * Extension.projectiveAction 1 hn x.val.right ModelClasses.longRight.val =
          ModelClasses.longRight.val * Extension.projectiveAction 1 hn 1 x.val.left
        simpa only [hfix,map_one,MulAut.one_apply] using hh
      · simp [longRight]
  rw [he]
  change _ ↔ x.val ∈ Extension.overlap 1 hn
  rw [Extension.binary_mem_overlap,←exact_overlap]
  have hlong : ModelClasses.longRight.val = ShortRootFixedFour.longPoint.val := rfl
  rw [hlong,←mem_centralizer_singleton_iff,ModelClasses.model_long_centralizer]
  exact (and_iff_left ((Extension.mem_plane 1 hn x.val).mp x.property)).symm


open BinaryPermutation
local notation "A" => AlternatingFiveExtension.AlternatingModel
local notation "S" => Multiplicative (core (Fin 5)) ⋊[AlternatingFiveExtension.coreAction] Equiv.Perm (Fin 5)
local notation "V" => Multiplicative (core (Fin 5))

/-- The original plane radical inside its literal degree-two extension. -/
def planeCore : Subgroup PE := (pCore 2 P).map Extension.binaryPlaneInclusion

/-- A single affine comparison preserves translations, the marked root
and its entire centralizer in the doubled endpoint. -/
theorem exists_marked_plane_equiv : ∃ E : S ≃* PE,
    E (SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)) = longRight ∧
    (SemidirectProduct.inl : V →* S).range.map E.toMonoidHom = planeCore ∧
    (centralizer ({SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)} : Set S)).map
      E.toMonoidHom = (Extension.overlap 1 hn).subgroupOf PE := by
  obtain ⟨e,hez,hecore,hecentral⟩ := AffinePlane.exists_marked_plane_equiv
  let i := Extension.binaryPlaneInclusion.comp e.toMonoidHom
  let ρ := (MulAut.congr e.symm).toMonoidHom.comp Extension.binaryPlaneConjugation
  have hi : Function.Injective i := Extension.binaryPlaneInclusion_injective.comp e.injective
  have hρ : Function.Injective ρ := (MulAut.congr e.symm).injective.comp
    Extension.binaryPlaneConjugation_injective
  have hρi (a : A) : ρ (i a) = MulAut.conj a := by
    change MulAut.congr e.symm (Extension.binaryPlaneConjugation (Extension.binaryPlaneInclusion (e a))) = _
    rw [Extension.binaryPlaneConjugation_inclusion]
    apply MulEquiv.ext
    intro x
    change e.symm (e a * e x * (e a)⁻¹) = a*x*a⁻¹
    rw [map_mul,map_mul,map_inv,e.symm_apply_apply,e.symm_apply_apply]
  have hQ : (SemidirectProduct.rightHom : A →* alternatingGroup (Fin 5)).ker = pCore 2 A := by
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    rw [←SemidirectProduct.range_inl_eq_ker_rightHom,hecore,pCore_map_iso]
  obtain ⟨f,hf⟩ := AlternatingFiveExtension.OuterRecognition.exists_marked_equiv_of_faithful_action
    i hi ρ hρ hρi (fun g => by rw [hQ]; exact pCore_map_iso 2 (ρ g)) Extension.binary_plane_card
  let E := f.symm
  have hE (v : V) : E (SemidirectProduct.inl v) =
      Extension.binaryPlaneInclusion (e (SemidirectProduct.inl v)) := by
    have hh := congrArg f.symm (hf v)
    rw [f.symm_apply_apply] at hh
    exact hh.symm
  have hz : E (SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)) = longRight := by
    rw [hE,hez]
    rfl
  refine ⟨E,hz,?_,?_⟩
  · have heq : E.toMonoidHom.comp (SemidirectProduct.inl : V →* S) =
        Extension.binaryPlaneInclusion.comp (e.toMonoidHom.comp (SemidirectProduct.inl : V →* A)) := by
      apply MonoidHom.ext
      intro v
      exact hE v
    rw [MonoidHom.map_range,heq,MonoidHom.range_comp,←MonoidHom.map_range,hecore]
    rfl
  · have hmap : (centralizer ({SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)} : Set S)).map
        E.toMonoidHom = centralizer ({longRight} : Set PE) := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        rw [←hz,mem_centralizer_singleton_iff]
        exact (map_mul E _ _).symm.trans
          ((congrArg E (mem_centralizer_singleton_iff.mp hx)).trans (map_mul E _ _))
      · intro hy
        refine ⟨E.symm y,?_,E.apply_symm_apply y⟩
        apply mem_centralizer_singleton_iff.mpr
        apply E.injective
        rw [map_mul,map_mul,E.apply_symm_apply,hz]
        exact mem_centralizer_singleton_iff.mp hy
    rw [hmap,right_long_centralizer]

end CFSG.Quasithin.ChapterF.UnitaryTwo.ExtendedAffinePlane

