module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.ProjectiveCoordinates
public import Theory.Combinatorics.TranslationPlane.ProjectiveActions

/-!
# Literal matrices for the original natural core and actor

The original core is exactly the native translation group under the
constructed projective incidence identification. The same original actor,
through its original SL₂ quotient, acts as a determinant-one affine matrix;
its translation part is the coordinate of the moved chosen origin. Equality
holds in the full collineation group, including the action on line covectors.

These are source-to-model action identities, with no perfectness restriction.
They prepare the simultaneous six-root construction in the centerfree branch
of DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224.
-/

@[expose] public noncomputable section
open Subgroup Configuration
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace ProjectiveCoordinates
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (d : SourceQuotient L S)
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k₁ W₁)
  (hn₀ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₀.actor : Set (generated L S)))
  (hn₁ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₁.actor : Set (generated L S)))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
  (hm : RootCoordinates.rotationOrder d = 3) (hcenter : centerIn c₁.actor = ⊥)

variable (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d})

/-- The whole original natural core has its literal native translation action. -/
theorem action_core (a : Q (fullFamily L S) (base (fullFamily L S) true)) :
    action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (d.q (a : generated L S)) =
      TranslationPlane.FieldChart.translation
        (OriginalCoordinates.coreCoordinates h c₀ c₁ E₁ hcenter a).toAdd := by
  classical
  apply Collineation.ext_affine (TranslationPlane.FieldChart.axis k₁)
  intro p hp
  obtain ⟨t,rfl⟩ := TranslationPlane.FieldChart.exists_point k₁ p hp
  rw [←pointCoordinates_affine h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t, action_point]
  rw [pointCoordinates_affine,TranslationPlane.FieldChart.translation_point]
  have ha := QuotientPlane.affineChart_add d h.generatedLocallyRankOneTriple
    c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o a t
  change (OriginalCoordinates.affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
    ((OriginalCoordinates.coreCoordinates h c₀ c₁ E₁ hcenter a).toAdd + t)).val =
      d.q (a : generated L S) •
        (OriginalCoordinates.affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val at ha
  rw [←ha,pointCoordinates_affine]

/-- Every native translation is obtained from the same original core map. -/
theorem action_core_parameter (t : Fin 2 → k₁) :
    action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (d.q ((OriginalCoordinates.coreCoordinates h c₀ c₁ E₁ hcenter).symm
        (.ofAdd t) : generated L S)) = TranslationPlane.FieldChart.translation t := by
  rw [action_core,MulEquiv.apply_symm_apply,toAdd_ofAdd]

/-- The affine displacement of the chosen origin by the original actor. -/
def actorDisplacement (a : c₁.actor) : Fin 2 → k₁ :=
  (OriginalCoordinates.affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).symm
    (QuotientPlane.actorAffineOrigin d c₁ o a)

/-- The actual natural-actor quotient is the linear part of its projective action. -/
theorem action_actor (a : c₁.actor) :
    action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (d.q (a : generated L S)) =
      TranslationPlane.FieldChart.affineCollineation (c₁.quotient a)
        (actorDisplacement h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o a) := by
  classical
  apply Collineation.ext_affine (TranslationPlane.FieldChart.axis k₁)
  intro p hp
  obtain ⟨t,rfl⟩ := TranslationPlane.FieldChart.exists_point k₁ p hp
  rw [←pointCoordinates_affine h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t,action_point,
    pointCoordinates_affine,TranslationPlane.FieldChart.affineCollineation_point]
  have ha := QuotientPlane.affineChart_actor d h.generatedLocallyRankOneTriple
    c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o a t
  have hb := QuotientPlane.affineChart_change_origin d h.generatedLocallyRankOneTriple
    c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (actorDisplacement h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o a)
      (Matrix.mulVec (c₁.quotient a).val t)
  have ho : OriginalCoordinates.affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (actorDisplacement h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o a) =
        QuotientPlane.actorAffineOrigin d c₁ o a := Equiv.apply_symm_apply _ _
  change (QuotientPlane.affineChart d h.generatedLocallyRankOneTriple c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter
      (OriginalCoordinates.affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
        (actorDisplacement h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o a))
      (Matrix.mulVec (c₁.quotient a).val t)).val = _ at hb
  rw [ho] at hb
  have hh := ha.symm.trans hb
  change d.q (a : generated L S) •
      (OriginalCoordinates.affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val =
    (OriginalCoordinates.affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (Matrix.mulVec (c₁.quotient a).val t +
        actorDisplacement h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o a)).val at hh
  rw [hh,pointCoordinates_affine]

/-- Every determinant-one affine matrix is realized by the SAME original actor.
Correcting its origin displacement uses its own natural core and keeps the
literal SL₂ quotient value. -/
theorem exists_actor_affine (A : SL(2,k₁)) (b : Fin 2 → k₁) :
    ∃ a : c₁.actor, c₁.quotient a = A ∧
      action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (d.q (a : generated L S)) =
        TranslationPlane.FieldChart.affineCollineation A b := by
  classical
  obtain ⟨a,ha⟩ := c₁.onto A
  let v := b - actorDisplacement h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o a
  let x := (OriginalCoordinates.coreCoordinates h c₀ c₁ E₁ hcenter).symm (.ofAdd v)
  let x' : c₁.actor := ⟨x,c₁.core_le x.property⟩
  have hx : c₁.quotient x' = 1 := by
    have hx' : x' ∈ c₁.quotient.ker := by
      rw [c₁.kernel]
      exact x.property
    exact hx'
  refine ⟨x' * a,by rw [map_mul,hx,one_mul,ha],?_⟩
  change action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
    (d.q ((x : generated L S) * (a : generated L S))) = _
  rw [map_mul,map_mul,action_core_parameter,action_actor,ha]
  apply Collineation.ext_affine (TranslationPlane.FieldChart.axis k₁)
  intro p hp
  obtain ⟨t,rfl⟩ := TranslationPlane.FieldChart.exists_point k₁ p hp
  change Collineation.pointHom _ _ (TranslationPlane.FieldChart.translation v)
    (Collineation.pointHom _ _ (TranslationPlane.FieldChart.affineCollineation A
      (actorDisplacement h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o a))
        (TranslationPlane.FieldChart.point k₁ t)) = _
  rw [TranslationPlane.FieldChart.affineCollineation_point,
    TranslationPlane.FieldChart.translation_point,TranslationPlane.FieldChart.affineCollineation_point]
  congr 1
  dsimp [v]
  abel

end ProjectiveCoordinates
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
