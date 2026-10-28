module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSix.Image
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Normalizer
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace
/-!
# Natural A6 actions force a six-letter ambient image

Conjugating the ambient operators into the literal natural four-space puts
them in the checked normalizer of A6, which is the natural S6 image. The
resulting six-letter homomorphism excludes minimal parabolicity regardless
of its kernel. Faithful four-spaces follow from the intrinsic A6 recognition.

Source: Aschbacher–Smith B.6.9 and K.1.1, printed pp.116 and 452.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource ChapterK.Alternating ChapterK.Alternating.RecognitionInputs.Six
open Representation.Hexacode.SixDimensional
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
/-- A normal natural A6 action cannot occur in a minimal parabolic. -/
theorem not_minimalParabolic_of_natural_alternatingSix
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (ρ : Representation (ZMod 2) G V)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 6)) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  classical
  let f := coordinateAction ρ e.linearEquiv
  have he (l : L) : f l = naturalLinearAction (e.groupEquiv l).val := by
    apply LinearEquiv.ext
    intro w
    change e.linearEquiv ((ρ.comp L.subtype) l (e.linearEquiv.symm w)) =
      alternatingNatural 6 (e.groupEquiv l) w
    rw [e.intertwines, e.linearEquiv.apply_symm_apply]
  have himage : L.map f = alternatingLinearImage := by
    ext t
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨e.groupEquiv ⟨l, hl⟩, (he ⟨l, hl⟩).symm⟩
    · rintro ⟨l, rfl⟩
      refine ⟨(e.groupEquiv.symm l).val, (e.groupEquiv.symm l).property, ?_⟩
      rw [he, e.groupEquiv.apply_symm_apply]
      rfl
  have hmem (g : G) : f g ∈ naturalLinearAction.range := by
    rw [← normalizer, ← himage]
    apply Subgroup.le_normalizer_map f
    exact ⟨g, by rw [L.normalizer_eq_top]; trivial, rfl⟩
  let j := f.codRestrict naturalLinearAction.range hmem
  let a : G →* Equiv.Perm (Fin 6) :=
    (MonoidHom.ofInjective six_naturalLinearAction_injective).symm.toMonoidHom.comp j
  have ha (g : G) : naturalLinearAction (a g) = f g :=
    MonoidHom.apply_ofInjective_symm six_naturalLinearAction_injective (j g)
  have hal (l : L) : a l = (e.groupEquiv l).val := by
    apply six_naturalLinearAction_injective
    rw [ha, he]
  have hr : alternatingGroup (Fin 6) ≤ a.range := by
    intro l hl
    refine ⟨(e.groupEquiv.symm ⟨l, hl⟩).val, ?_⟩
    rw [hal, e.groupEquiv.apply_symm_apply]
  exact not_minimalParabolic_of_six_image T a hr
/-- The same exclusion holds for any faithful A6 four-space restriction. -/
theorem not_minimalParabolic_of_alternatingSix_fourSpace [FiniteDimensional (ZMod 2) V]
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (ρ : Representation (ZMod 2) G V) (e : L ≃* alternatingGroup (Fin 6))
    (hf : Function.Injective (ρ.comp L.subtype))
    (hd : Module.finrank (ZMod 2) V = 4) : ¬ IsMinimalParabolicOver T ⊤ := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  obtain ⟨c⟩ := actionEquiv_of_faithful_fourSpace σ (hf.comp e.symm.injective) hd
  apply not_minimalParabolic_of_natural_alternatingSix T L ρ
  refine ⟨e.trans c.groupEquiv,c.linearEquiv,?_⟩
  intro l v
  have hh := c.intertwines (e l) v
  change c.linearEquiv (ρ ((e.symm (e l) : L) : G) v) = _ at hh
  simpa only [e.symm_apply_apply,MonoidHom.comp_apply,Subgroup.subtype_apply,MulEquiv.trans_apply] using hh
end CFSG.Quasithin.ChapterB
