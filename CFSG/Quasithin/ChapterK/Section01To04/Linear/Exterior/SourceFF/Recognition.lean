module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.Setup
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Core
public import Theory.Representation.BinaryLinearRecognition
public import Theory.Representation.Quotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The original ten-dimensional SL₅ component

The exhaustive ten-dimensional module theorem supplies the exterior square
or cube on the original component. Hodge duality carries the cube to the
square with its inverse-transpose twist retained in the group identification.
The actual self-normalizing exterior image then forces the original normal
component to be the whole faithful ambient group.

Source: Aschbacher–Smith K.3.2.3, printed p.455, and I.1.6(7), p.408.
-/

public section
noncomputable section
open Representation Subgroup Theory.GroupTheory
open Representation.SL5TenDimensional
namespace CFSG.Quasithin.ChapterK.Linear.Exterior.SourceFF
open ChapterB.QuasisimpleSource
variable {G V : Type*} [_root_.Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {K : GroupClass}

theorem exteriorAction_of_finrank (h : Recognition.SourceHypothesis K ρ L)
    (e₀ : L ≃* Group) (hd : Module.finrank (ZMod 2) V = 10) :
    Nonempty (ActionEquiv (ρ.comp L.subtype) (exteriorAction 2)) := by
  let σ := (ρ.comp L.subtype).comp e₀.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e₀.symm.toMonoidHom e₀.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  rcases Classification.identification_of_finrank_ten σ hd with hf | hf
  · obtain ⟨f⟩ := hf
    refine ⟨⟨e₀, f.toLinearEquiv, ?_⟩⟩
    intro l v
    have he := IntertwiningMap.isIntertwining σ (exteriorAction 2)
      f.toIntertwiningMap (e₀ l) v
    simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e₀.symm_apply_apply, Representation.Equiv.toLinearEquiv_apply] using he
  · obtain ⟨f⟩ := hf
    refine ⟨⟨e₀.trans SL5ExteriorSquare.Duality.graph,
      f.toLinearEquiv.trans SL5ExteriorSquare.Duality.hodge, ?_⟩⟩
    intro l v
    have he := IntertwiningMap.isIntertwining σ (exteriorAction 3)
      f.toIntertwiningMap (e₀ l) v
    have he' : f.toLinearEquiv ((ρ.comp L.subtype) l v) =
        exteriorAction 3 (e₀ l) (f.toLinearEquiv v) := by
      simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        e₀.symm_apply_apply, Representation.Equiv.toLinearEquiv_apply] using he
    exact (congrArg SL5ExteriorSquare.Duality.hodge he').trans
      (SL5ExteriorSquare.Duality.hodge_action (e₀ l) (f.toLinearEquiv v))

theorem whole_of_exterior (h : Recognition.SourceHypothesis K ρ L)
    (e : ActionEquiv (ρ.comp L.subtype) (exteriorAction 2)) : L = ⊤ := by
  let := h.finite_group
  let : L.Normal := h.fitting ▸ inferInstance
  exact BinaryLinearRecognition.eq_top_of_self_normalizing_image ρ (exteriorAction 2)
    h.faithful L e.groupEquiv e.linearEquiv e.intertwines ExteriorNormalizer.normalizer_two

end CFSG.Quasithin.ChapterK.Linear.Exterior.SourceFF
