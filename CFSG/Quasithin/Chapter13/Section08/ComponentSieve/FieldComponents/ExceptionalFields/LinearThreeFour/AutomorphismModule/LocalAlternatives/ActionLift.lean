module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.Constructions
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Lifting the prescribed source action from PSL₃(4) to SL₃(4)

The automorphism here is conjugation by the inverse of the prescribed element
of H*, transported through the actual K* ≃ SL₃(4) equivalence. This convention
is exactly the one required by the natural-plus-dual coordinate construction.
Perfectness makes the action of Aut(SL₃(4)) on SL₃(4)/Z faithful, so a
projective linear–graph form determines the actual special linear action.
No involution assumption or alternative central cover is used.

This is a transfer lemma, not the classification of that projective action.
Source: Aschbacher–Smith, proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Representation.SL3FourNaturalDual
open Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
variable {G : Type*} [Group G]

private theorem centerAction_injective : Function.Injective (centerAction F) := by
  let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
  have he : centerAction F = Subgroup.quotientAut (center SL) := by
    ext a x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center SL) x
    change centerAction F a (QuotientGroup.mk y) =
      (center SL).quotientAut a ((QuotientGroup.mk' (center SL)) y)
    rw [centerAction_mk, Subgroup.quotientAut_apply_mk]
    rfl
  rw [he]
  exact MulAut.quotient_center_injective

/-- Conjugation by the prescribed t inverse, transported along the actual model equivalence. -/
def sourceConjugation (H K : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H) : MulAut SL :=
  MulAut.congr eK (MulAut.conjNormal t⁻¹)

theorem sourceActor_sourceConjugation (H K : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H) (g : SL) :
    sourceActor H K eK (sourceConjugation H K eK t g) =
      t⁻¹ * sourceActor H K eK g * t := by
  change (eK.symm (eK (MulAut.conjNormal t⁻¹ (eK.symm g)))).val = _
  rw [eK.symm_apply_apply, MulAut.conjNormal_apply, inv_inv]
  rfl

/-- Projective agreement determines the actual SL₃(4) automorphism. -/
theorem sourceConjugation_eq_of_projective (H K : Subgroup G)
    [(Source.starImage H K).Normal] (eK : Source.starImage H K ≃* SL)
    (t : Source.Hstar H) (α : MulAut SL)
    (h : centerAction F (sourceConjugation H K eK t) = centerAction F α) :
    sourceConjugation H K eK t = α := centerAction_injective h

/-- Lift a projective graph form to the literal relation required by the marking. -/
theorem source_graph_relation (H K : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H)
    (c : Matrix.GeneralLinearGroup (Fin 3) F)
    (h : centerAction F (sourceConjugation H K eK t) = linearConj F c * graph F) :
    ∀ g, sourceActor H K eK g * t = t * sourceActor H K eK
      (linearConjSL F c (Matrix.SpecialLinearGroup.inverseTranspose g)) := by
  have he : sourceConjugation H K eK t = linearConjSL F c * graphSL F := by
    apply sourceConjugation_eq_of_projective H K eK t
    rw [map_mul]
    exact h
  have hgraph (g : SL) : graphSL F g = Matrix.SpecialLinearGroup.inverseTranspose g := by
    apply Subtype.ext
    exact (Matrix.adjugate_transpose g.val).symm
  intro g
  have hg := sourceActor_sourceConjugation H K eK t g
  rw [he, MulAut.mul_apply, hgraph] at hg
  calc
    _ = t * (t⁻¹ * sourceActor H K eK g * t) := by group
    _ = _ := congrArg (t * ·) hg.symm
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
