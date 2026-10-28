module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.Source
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Faithful binary actions of an almost simple Tits group have no offender

The internal displacement calculation requires no irreducibility. Every
involution in an almost simple Tits overgroup is inner on its same normal
simple subgroup, so a trivial centralizer places every elementary actor
inside that subgroup. Restriction preserves its exact offender inequality.

Source: Guralnick--Malle II, Lemma8.8; Aschbacher--Smith6.1.4 and B.4.2.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterK.Exceptional.TitsCubicDisplacement
variable {G W : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem tits_not_ff (σ : Representation (ZMod 2) Tits.ParrottGroup W)
    (hf : Function.Injective σ) : ¬ IsFFModule σ := by
  rintro ⟨A,hA⟩
  have hh := ElementaryGeometry.internal_displacement_of_coverage_and_weights
    Tits.InvolutionRootGeometry.binaryInvolutionCoverage σ hf
    (fiveKernel_fixedCodim_ge_twenty σ hf) (fiveInverter_fixedCodim_ge_twelve σ hf) A hA.1
  have hb := hA.2
  omega

/-- Every elementary actor belongs to the same normal self-centralizing
Tits subgroup. This retains the actual ambient elements. -/
theorem elementary_le_normal_tits (N A : Subgroup G) [N.Normal]
    (e : N ≃* Tits.ParrottGroup) (hc : centralizer (N : Set G) = ⊥)
    (hA : IsElementaryAbelian 2 A) : A ≤ N := by
  let := hA
  have hj : Function.Injective (MulAut.conjNormal : G →* MulAut N) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [MulAut.conjNormal_ker_eq_centralizer,hc]
  intro a ha
  let α := (MulAut.congr e) (MulAut.conjNormal a)
  have hα : α^2 = 1 := by
    rw [←map_pow,←map_pow,elemPow_eq_one_of_isElementaryAbelian a ha,map_one,map_one]
  obtain ⟨x,_,hx⟩ := inner_from_binary_coverage
    Tits.InvolutionRootGeometry.binaryInvolutionCoverage α hα
  let y := e.symm x
  have hy : (MulAut.conjNormal a : MulAut N) = MulAut.conjNormal (y:G) := by
    apply (MulAut.congr e).injective
    rw [show (MulAut.congr e) (MulAut.conjNormal a) = α from rfl,hx]
    ext z
    change x*z*x⁻¹ = e (y * e.symm z * y⁻¹)
    simp only [map_mul,map_inv,y,e.apply_symm_apply]
  have hay : a = (y:G) := hj hy
  exact hay ▸ y.property

/-- No faithful binary action with a normal self-centralizing Tits
subgroup has an FF offender; no irreducibility is assumed. -/
theorem normal_tits_not_ff (ρ : Representation (ZMod 2) G W)
    (N : Subgroup G) [N.Normal] (e : N ≃* Tits.ParrottGroup)
    (hc : centralizer (N : Set G) = ⊥) (hf : Function.Injective ρ) :
    ¬ IsFFModule ρ := by
  rintro ⟨A,hA⟩
  have hAN := elementary_le_normal_tits N A e hc hA.1.2
  have hrest := hA.subgroupOf ρ hAN
  let σ := (ρ.comp N.subtype).comp e.symm.toMonoidHom
  have hσ : Function.Injective σ := (hf.comp N.subtype_injective).comp e.symm.injective
  apply tits_not_ff σ hσ
  refine ⟨(A.subgroupOf N).map e.toMonoidHom,
    hrest.map_equivariant (ρ.comp N.subtype) σ e.toMonoidHom e.injective
      (LinearEquiv.refl _ _) ?_⟩
  intro a w
  change ρ (a:G) w = ρ ((e.symm (e a):N):G) w
  rw [e.symm_apply_apply]

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
