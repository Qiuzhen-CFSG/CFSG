module
public import Theory.Representation.SL2NaturalOffenders.Ratios
public import Theory.Representation.BinaryOffender.NormalizerNonStrong

/-!
# Natural SL₂ sections have no strong offenders

The full binary linear normalizer of the natural SL₂ module has no strong
FF offender. A compatible quotient action detects the kernel on each natural
section, so a faithful elementary actor costs at least its rank there.
This supplies the section estimate used in Aschbacher--Smith D.3.21(3),
printed pp.205--206, without assuming that the full normalizer is a two-group.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.SL2NaturalOffenders
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

omit [Finite F] in
theorem natural_injective : Function.Injective (NoStrong.natural (F := F)) := by
  intro g h he
  apply Subtype.ext
  apply Matrix.mulVec_injective
  exact funext (fun v => LinearMap.congr_fun he v)

theorem normalizer_not_strong (hF : 2 < Nat.card F) :
    ¬ IsStrongFFModule (normalizerRepresentation (NoStrong.natural (F := F))) := by
  let μ := NoStrong.natural (F := F)
  let : Finite (Module.End (ZMod 2) (Fin 2 → F)) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) (Fin 2 → F) => (f : (Fin 2 → F) → (Fin 2 → F)))
      DFunLike.coe_injective
  let : Finite (Module.End (ZMod 2) (Fin 2 → F))ˣ :=
    Finite.of_injective Units.val Units.val_injective
  let Q := linearNormalizer μ
  let K := (actionImage μ).subgroupOf Q
  have hle : actionImage μ ≤ Q := (actionImage μ).le_normalizer
  let : K.Normal := (normal_subgroupOf_iff_le_normalizer hle).mpr le_rfl
  let e : K ≃* NoStrong.Actor F := (subgroupOfEquivOfLe hle).trans
    (MonoidHom.ofInjective (show Function.Injective μ.asGroupHom from by
      intro g h he
      exact natural_injective (congrArg Units.val he))).symm
  have hn (g : K) (v : Fin 2 → F) :
      normalizerRepresentation μ (g : Q) v = (e g).val.mulVec v := by
    have hg := (MonoidHom.ofInjective (show Function.Injective μ.asGroupHom from by
      intro g h he
      exact natural_injective (congrArg Units.val he))).apply_symm_apply
      (subgroupOfEquivOfLe hle g)
    exact congrArg (fun z : actionImage μ => z.val.val v) hg.symm
  have hf : Function.Injective (normalizerRepresentation μ) := by
    intro x y h
    apply Subtype.ext
    exact Units.ext h
  exact Ratios.not_strong K e (normalizerRepresentation μ) hn hF hf

end Representation.SL2NaturalOffenders

namespace Representation.SL2NaturalOffenders
open Representation.BinaryOffender
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem rank_le_fixedCodim_of_natural_section
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
    (q : N →* NoStrong.Actor F) (hq : Function.Surjective q)
    (α : G →* MulAut (NoStrong.Actor F))
    (hα : ∀ (a : G) (k : N), q (MulAut.conjNormal a k) = α a (q k))
    (b : Representation.Equiv (ρ.comp N.subtype) (NoStrong.natural.comp q))
    (hF : 2 < Nat.card F)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hf : Function.Injective (α.comp A.subtype)) :
    rank A ≤ fixedCodim ρ A := by
  have hfaith := faithful_actor_of_marked_normal_action ρ N
    (NoStrong.natural (F := F)) (natural_injective (F := F)) q hq α hα b A hf
  have hi : N.subtype.range = N := Subgroup.range_subtype N
  have hN : N.Normal := inferInstance
  let : N.subtype.range.Normal := hi.symm ▸ hN
  have hn := image_not_strong_of_marked_normal_range ρ N.subtype (NoStrong.natural (F := F)) q hq b
    (normalizer_not_strong (F := F) hF)
  by_contra! hlt
  apply hn
  refine ⟨actionSubgroup ρ A,hA.actionSubgroup ρ hfaith,?_⟩
  rw [fixedCodim_actionSubgroup,actionSubgroup_rank ρ A hfaith]
  exact hlt
end Representation.SL2NaturalOffenders
