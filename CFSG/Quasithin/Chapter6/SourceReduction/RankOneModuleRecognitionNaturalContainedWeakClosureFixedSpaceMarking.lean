module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureFixedSpaceGeometry
public import CFSG.Quasithin.Chapter6.Section02.NaturalSylowGeometry
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The actual binary action in the natural-module coordinates

The chosen multiplicative marking gives binary linear coordinates. Conjugation
on L induces an automorphism of the literal quotient L/O₂(L). Equivariance
then intertwines this automorphism with the actual automizer on B. The scalar
commutant of natural SL₂ proves semilinearity, preserving every coordinate map.
Source: Aschbacher--Smith, 6.1.6--12, printed pp.669--670.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterE Representation.SL2NaturalOffenders
open CFSG.Quasithin.Chapter6.Source
open scoped IsMulCommutative

variable {G : Type*} [Group G] {L B : Subgroup G}
  [IsElementaryAbelian 2 B]
  {F : Type} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The original quotient and module markings make ambient normalizers semilinear. -/
theorem natural_binary_marking_semilinear (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : B ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (l : L) (v : B),
      (f.symm (Multiplicative.ofAdd
        (Matrix.mulVec (e (QuotientGroup.mk' (pCore 2 L) l)).val (f v).toAdd)) : G) =
        (l : G) * (v : G) * (l : G)⁻¹) :
    ∃ E : Additive B ≃ₗ[ZMod 2] (Fin 2 → F),
      (∀ v : B, E (Additive.ofMul v) = (f v).toAdd) ∧
      ∀ a : G, a ∈ normalizer (L : Set G) → ∀ haB : a ∈ normalizer (B : Set G),
      ∃ σ : F ≃+* F, ∀ c v,
        E (automizerRepresentation B (B.normalizerMonoidHom.rangeRestrict ⟨a,haB⟩)
          (E.symm (c • v))) =
        σ c • E (automizerRepresentation B (B.normalizerMonoidHom.rangeRestrict ⟨a,haB⟩)
          (E.symm v)) := by
  let E : Additive B ≃ₗ[ZMod 2] (Fin 2 → F) :=
    LinearEquiv.ofBijective (f.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) f.bijective
  refine ⟨E,fun _ => rfl,?_⟩
  intro a haL haB
  let β := B.normalizerMonoidHom ⟨a,haB⟩
  let α := L.normalizerMonoidHom ⟨a,haL⟩
  let γ := MulAut.congr e (quotientAut (pCore 2 L) α)
  let ρ : Representation (ZMod 2) (Automizer B) (Fin 2 → F) :=
    E.conjRingEquiv.toMonoidHom.comp (automizerRepresentation B)
  let t := B.normalizerMonoidHom.rangeRestrict ⟨a,haB⟩
  let d := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)
  have hd (v : B) : d (f v).toAdd = (f (β v)).toAdd := by
    change E (automizerRepresentation B t (E.symm (E (Additive.ofMul v)))) = _
    rw [E.symm_apply_apply]
    rfl
  have hg (l : L) : γ (e (QuotientGroup.mk' (pCore 2 L) l)) =
      e (QuotientGroup.mk' (pCore 2 L) (α l)) := by
    simp only [γ, MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply,
      quotientAut_apply_mk]
  have heq (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
      d (g.val.mulVec v) = (γ g).val.mulVec (d v) := by
    obtain ⟨l, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    obtain ⟨w, hw⟩ := f.surjective (Multiplicative.ofAdd v)
    have hw' : (f w).toAdd = v := congrArg Multiplicative.toAdd hw
    change d ((e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec v) =
      (γ (e (QuotientGroup.mk' (pCore 2 L) l))).val.mulVec (d v)
    rw [← hw',hd,hg]
    let u := f.symm (Multiplicative.ofAdd
      ((e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (f w).toAdd))
    have hu : (f u).toAdd =
        (e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (f w).toAdd :=
      congrArg Multiplicative.toAdd (f.apply_symm_apply _)
    rw [← hu,hd]
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    simp only [ofAdd_toAdd, f.symm_apply_apply]
    apply Subtype.ext
    rw [hf, normalizerMonoidHom_apply_apply_coe,
      normalizerMonoidHom_apply_apply_coe, normalizerMonoidHom_apply_apply_coe]
    change a * (u : G) * a⁻¹ = _
    rw [show (u : G) = (l : G) * (w : G) * (l : G)⁻¹ from hf l w]
    group
  exact Representation.OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
    (Representation.specialLinearNatural 2 (k := F))
    (fun k hk => centralizer_scalar k hk) γ d heq

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
