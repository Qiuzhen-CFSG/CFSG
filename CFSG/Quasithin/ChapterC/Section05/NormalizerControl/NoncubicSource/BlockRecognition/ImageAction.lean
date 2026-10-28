module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
/-!
# The actual full block module and its faithful action image

A surjection with exact two-core kernel identifies the intrinsic quotient
actor, and the moved-space realization identifies the full U(L). The
intertwiner retains the literal conjugation formula and all central layers.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ChapterB.QuasisimpleSource ExceptionalRestrictions
variable {L H W : Type*} [Group L] [Group H] [AddCommGroup W] [Module (ZMod 2) W]

theorem blockU_actionEquiv_of_image (h : IsShort L)
    (ρ : Representation (ZMod 2) H W) (f : L →* H) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 L)
    (j : Multiplicative W →* L) (hj : Function.Injective j) (hr : j.range = blockU L)
    (he : ∀ l w, j (Multiplicative.ofAdd (ρ (f l) w)) = l * j (Multiplicative.ofAdd w) * l⁻¹) :
    letI := h.elementary
    Nonempty (ActionEquiv (uRepresentation h) ρ) := by
  let := h.elementary
  let E : Multiplicative W ≃* blockU L :=
    (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hr)
  let e : W ≃ₗ[ZMod 2] Additive (blockU L) :=
    { E.toAdditive with map_smul' := fun a w => ZMod.map_smul E.toAdditive a w }
  let a : (L ⧸ pCore 2 L) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have ha (l : L) : a (QuotientGroup.mk' (pCore 2 L) l) = f l := rfl
  refine ⟨⟨a,e.symm,?_⟩⟩
  intro g u
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) g
  rw [ha]
  apply e.injective
  rw [e.apply_symm_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change l * (u.toMul : L) * l⁻¹ = j (Multiplicative.ofAdd (ρ (f l) (e.symm u)))
  rw [he]
  have hh : j (Multiplicative.ofAdd (e.symm u)) = (u.toMul : L) :=
    congrArg (fun v : Additive (blockU L) => (v.toMul : L)) (e.apply_symm_apply u)
  rw [hh]
end CFSG.Quasithin.ChapterC
