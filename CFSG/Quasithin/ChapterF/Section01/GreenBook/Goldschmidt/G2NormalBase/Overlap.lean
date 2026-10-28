module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.Goldschmidt.G2NormalBase.Model
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ModelResidualAction

/-!
# The original overlap in the full binary G₂ Borel

The faithful action on the marked derived model identifies the original
overlap with a subgroup of the full binary Borel. On the residual overlap
this map is its literal ambient inclusion. Conjugation on each endpoint is
therefore retained, and membership in the derived Borel detects membership
in the actual ambient two-residual. Source: Goldschmidt (1980), §3.7.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.G2NormalBase
open Subgroup Theory.GroupTheory RankTwoAmalgam
open SourceAssembly.Goldschmidt ExceptionalModels.G2
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

abbrev baseAmalgam (F : Bool → Subgroup G) :=
  inclusionAmalgam (residualFamily F false) (residualFamily F true)

def baseOverlapEmbedding (F : Bool → Subgroup G) :
    ↥(residualFamily F false ⊓ residualFamily F true) →* ↥(F false ⊓ F true) where
  toFun s := ⟨s.val.val, s.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def overlapHom (e : Iso (baseAmalgam F) simpleAmalgam) :
    ↥(F false ⊓ F true) →* fullB :=
  Model.fullBorelActionEquiv.symm.toMonoidHom.comp (modelResidualAction F e)

theorem overlapHom_injective (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) simpleAmalgam) : Function.Injective (overlapHom e) :=
  Model.fullBorelActionEquiv.symm.injective.comp (h.modelResidualAction_injective e)

private theorem action_overlapHom (e : Iso (baseAmalgam F) simpleAmalgam)
    (t : ↥(F false ⊓ F true)) :
    Model.fullBorelActionEquiv (overlapHom e t) = modelResidualAction F e t :=
  Model.fullBorelActionEquiv.apply_symm_apply _

theorem overlapHom_left (e : Iso (baseAmalgam F) simpleAmalgam)
    (t : ↥(F false ⊓ F true)) (n : residualFamily F false) :
    (overlapHom e t : Full) * (e.left n).val.val * (overlapHom e t : Full)⁻¹ =
      (e.left ((residualAmalgamAction F t).left n)).val.val := by
  have he := congrArg (fun a : Iso simpleAmalgam simpleAmalgam =>
    (a.left (e.left n)).val.val) (action_overlapHom e t)
  have he' := (Model.action_left (overlapHom e t) (e.left n)).symm.trans he
  change _ = (e.left ((residualAmalgamAction F t).left (e.left.symm (e.left n)))).val.val at he'
  simpa only [e.left.symm_apply_apply] using he'

theorem overlapHom_middle (e : Iso (baseAmalgam F) simpleAmalgam)
    (t : ↥(F false ⊓ F true)) (n : ↥(residualFamily F false ⊓ residualFamily F true)) :
    (overlapHom e t : Full) * (e.middle n).val.val * (overlapHom e t : Full)⁻¹ =
      (e.middle ((residualAmalgamAction F t).middle n)).val.val := by
  have he := congrArg (fun a : Iso simpleAmalgam simpleAmalgam =>
    (a.middle (e.middle n)).val.val) (action_overlapHom e t)
  have he' := (Model.action_middle (overlapHom e t) (e.middle n)).symm.trans he
  change _ = (e.middle ((residualAmalgamAction F t).middle
    (e.middle.symm (e.middle n)))).val.val at he'
  simpa only [e.middle.symm_apply_apply] using he'

theorem overlapHom_right (e : Iso (baseAmalgam F) simpleAmalgam)
    (t : ↥(F false ⊓ F true)) (n : residualFamily F true) :
    (overlapHom e t : Full) * (e.right n).val.val * (overlapHom e t : Full)⁻¹ =
      (e.right ((residualAmalgamAction F t).right n)).val.val := by
  have he := congrArg (fun a : Iso simpleAmalgam simpleAmalgam =>
    (a.right (e.right n)).val.val) (action_overlapHom e t)
  have he' := (Model.action_right (overlapHom e t) (e.right n)).symm.trans he
  change _ = (e.right ((residualAmalgamAction F t).right (e.right.symm (e.right n)))).val.val at he'
  simpa only [e.right.symm_apply_apply] using he'

private theorem map_conjugate_of_eq {K H : Type*} [Group K] [Group H]
    (f : K →* H) {a n z : K} (hz : z = a * n * a⁻¹) {b : H} (hb : f a = b) :
    f z = b * f n * b⁻¹ := by
  rw [hz, map_mul, map_mul, map_inv, hb]

/-- On the marked residual overlap the full Borel element is exactly the
original derived-group element. -/
theorem overlapHom_base (e : Iso (baseAmalgam F) simpleAmalgam)
    (s : ↥(residualFamily F false ⊓ residualFamily F true)) :
    overlapHom e (baseOverlapEmbedding F s) = Model.innerBEmbedding (e.middle s) := by
  apply Model.fullBorelAction_injective
  apply Iso.ext
  · apply MulEquiv.ext
    refine e.left.surjective.forall.mpr (fun n => ?_)
    apply Subtype.ext
    apply Subtype.ext
    have hc : (residualAmalgamAction F (baseOverlapEmbedding F s)).left n =
        (baseAmalgam F).left s * n * ((baseAmalgam F).left s)⁻¹ := rfl
    have hm : (e.left ((residualAmalgamAction F (baseOverlapEmbedding F s)).left n)).val.val =
        (e.middle s).val.val * (e.left n).val.val * (e.middle s).val.val⁻¹ := by
      let f : residualFamily F false →* Full :=
        Derived.subtype.comp (derivedL₁.subtype.comp e.left.toMonoidHom)
      exact map_conjugate_of_eq f hc
        (congrArg (fun x : derivedL₁ => x.val.val) (e.left_commutes s))
    exact (Model.fullBorelAction_left_apply
      (overlapHom e (baseOverlapEmbedding F s)) (e.left n)).trans
      ((overlapHom_left e (baseOverlapEmbedding F s) n).trans
        (hm.trans (Model.fullBorelAction_left_apply
          (Model.innerBEmbedding (e.middle s)) (e.left n)).symm))
  · apply MulEquiv.ext
    refine e.middle.surjective.forall.mpr (fun n => ?_)
    apply Subtype.ext
    apply Subtype.ext
    have hc : (residualAmalgamAction F (baseOverlapEmbedding F s)).middle n = s*n*s⁻¹ := rfl
    have hm : (e.middle ((residualAmalgamAction F (baseOverlapEmbedding F s)).middle n)).val.val =
        (e.middle s).val.val * (e.middle n).val.val * (e.middle s).val.val⁻¹ := by
      let f : ↥(residualFamily F false ⊓ residualFamily F true) →* Full :=
        Derived.subtype.comp (derivedB.subtype.comp e.middle.toMonoidHom)
      exact map_conjugate_of_eq f hc rfl
    exact (Model.fullBorelAction_middle_apply
      (overlapHom e (baseOverlapEmbedding F s)) (e.middle n)).trans
      ((overlapHom_middle e (baseOverlapEmbedding F s) n).trans
        (hm.trans (Model.fullBorelAction_middle_apply
          (Model.innerBEmbedding (e.middle s)) (e.middle n)).symm))
  · apply MulEquiv.ext
    refine e.right.surjective.forall.mpr (fun n => ?_)
    apply Subtype.ext
    apply Subtype.ext
    have hc : (residualAmalgamAction F (baseOverlapEmbedding F s)).right n =
        (baseAmalgam F).right s * n * ((baseAmalgam F).right s)⁻¹ := rfl
    have hm : (e.right ((residualAmalgamAction F (baseOverlapEmbedding F s)).right n)).val.val =
        (e.middle s).val.val * (e.right n).val.val * (e.middle s).val.val⁻¹ := by
      let f : residualFamily F true →* Full :=
        Derived.subtype.comp (derivedL₂.subtype.comp e.right.toMonoidHom)
      exact map_conjugate_of_eq f hc
        (congrArg (fun x : derivedL₂ => x.val.val) (e.right_commutes s))
    exact (Model.fullBorelAction_right_apply
      (overlapHom e (baseOverlapEmbedding F s)) (e.right n)).trans
      ((overlapHom_right e (baseOverlapEmbedding F s) n).trans
        (hm.trans (Model.fullBorelAction_right_apply
          (Model.innerBEmbedding (e.middle s)) (e.right n)).symm))

theorem overlap_range_cases (e : Iso (baseAmalgam F) simpleAmalgam) :
    (overlapHom e).range = Model.innerBEmbedding.range ∨ (overlapHom e).range = ⊤ := by
  apply Model.intermediate_fullB_eq
  rintro _ ⟨b, rfl⟩
  obtain ⟨s, rfl⟩ := e.middle.surjective b
  exact ⟨baseOverlapEmbedding F s, overlapHom_base e s⟩

theorem overlapHom_mem_inner_iff (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) simpleAmalgam) (t : ↥(F false ⊓ F true)) :
    overlapHom e t ∈ Model.innerBEmbedding.range ↔ (t : G) ∈ pResidual 2 G := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨s, rfl⟩ := e.middle.surjective b
    have he : baseOverlapEmbedding F s = t :=
      overlapHom_injective h e ((overlapHom_base e s).trans hb)
    exact he ▸ s.val.property
  · intro ht
    let s : ↥(residualFamily F false ⊓ residualFamily F true) := ⟨⟨t, ht⟩, t.property⟩
    exact ⟨e.middle s, (overlapHom_base e s).symm⟩

end CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.G2NormalBase
