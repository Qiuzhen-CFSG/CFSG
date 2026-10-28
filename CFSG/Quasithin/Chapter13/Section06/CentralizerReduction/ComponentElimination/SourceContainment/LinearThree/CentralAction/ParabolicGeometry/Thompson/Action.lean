module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.Setup

/-!
# The full-action interface for the doubled-module calculation

`ExtendedCoordinates` specifies the actual action of the full plus quotient
on U_K in a given doubled marking. It requires equivariance, faithfulness,
and normalization of the literal diagonal SL₃(2), and asserts no offender,
Thompson, Baumann, or parabolic identification. Its construction under
hypothetical centrality is a remaining source obligation.

The original centralizer Sylow does restrict to the plus actor. Its image
is Sylow in the faithful matrix action image, so the model calculation
needs only Sylow subgroups of groups between the diagonal component and
its full linear normalizer, rather than an assumed whole-normalizer image.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation BinaryLinearThree
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
open ComponentSelection
variable {G : Type*} [_root_.Group G]
    {K L T : Subgroup G} {z v : G}

/-- A genuine extension of the component marking to the entire plus actor.
Constructing this is separate from calculating offenders in its Sylow image. -/
structure ExtendedCoordinates (e : EarlierData K L T z v)
    (d : DoubledCoordinates K L T z v e.selected.1.1 e.normalizeL e.fixSeed) where
  normalizes : plusActor K L T v ≤ normalizer (UK K L T z v : Set G)
  action : Gplus K L T z v e.normalizeL e.fixSeed →*
    (Module.End (ZMod 2) (Vector × Vector))ˣ
  faithful : Function.Injective action
  on_component : action.comp (modelEmbedding d) = (W.prod W).asGroupHom
  equivariant : ∀ (a : plusActor K L T v) (u : UK K L T z v),
    d.moduleEquiv (conjugationAction _ _ normalizes a u) =
      Multiplicative.ofAdd
        ((action (plusMk K L T z v e.normalizeL e.fixSeed a) :
          Module.End (ZMod 2) (Vector × Vector)) (d.moduleEquiv u).toAdd)
  normalizes_diagonal : action.range ≤
    normalizer ((W.prod W).asGroupHom.range : Set (Module.End (ZMod 2) (Vector × Vector))ˣ)

namespace EarlierData
variable (e : EarlierData K L T z v)

/-- The literal T_v inside the plus actor is an actual Sylow subgroup. -/
theorem internalR_isSylow : ∃ Q : Sylow 2 (plusActor K L T v),
    (Q : Subgroup (plusActor K L T v)) = e.internalR := by
  obtain ⟨P, hP⟩ := e.tvSylow
  obtain ⟨Q, hQ⟩ := P.exists_map_subtype_eq_of_le
    (plusActor_le_Gv K L T v e.selected.1.1)
    (show (P : Subgroup (Gv v)).map (Gv v).subtype ≤ plusActor K L T v by
      rw [hP]; exact le_sup_right)
  refine ⟨Q, ?_⟩
  apply map_injective (plusActor K L T v).subtype_injective
  rw [hQ, hP, internalR,
    map_subgroupOf_eq_of_le (show Tv T v ≤ plusActor K L T v from le_sup_right)]

end EarlierData

namespace ExtendedCoordinates
variable {e : EarlierData K L T z v}
    {d : DoubledCoordinates K L T z v e.selected.1.1 e.normalizeL e.fixSeed}
    (c : ExtendedCoordinates e d)

/-- The matrix action image contains the whole diagonal component. -/
theorem diagonal_le_range : (W.prod W).asGroupHom.range ≤ c.action.range := by
  rw [← c.on_component]
  rintro _ ⟨x, rfl⟩
  exact ⟨modelEmbedding d x, rfl⟩

/-- The actual image of T_v is Sylow in the matrix action image. -/
theorem sylow_image [Finite G] : ∃ P : Sylow 2 c.action.range,
    (P : Subgroup c.action.range).map c.action.range.subtype =
      (plusImage K L T z v e.normalizeL e.fixSeed (Tv T v)).map c.action := by
  obtain ⟨Q, hQ⟩ := e.internalR_isSylow
  let f := c.action.rangeRestrict.comp (plusMk K L T z v e.normalizeL e.fixSeed)
  have hf : Function.Surjective f := c.action.rangeRestrict_surjective.comp
    (plusMk_surjective K L T z v e.normalizeL e.fixSeed)
  refine ⟨Q.mapSurjective hf, ?_⟩
  rw [Sylow.coe_mapSurjective]
  rw [map_map, hQ]
  change e.internalR.map (c.action.comp (plusMk K L T z v e.normalizeL e.fixSeed)) = _
  rw [← map_map]
  rfl

end ExtendedCoordinates
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
