module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearChiefNonzero
public import Theory.Representation.SL3.AdjointCubicCentralizer.TwistedNatural

/-!
# The faithful binary determinant twist at the original L-plus marking

Apply the concrete projective model over the chosen module's own field and
pull its lower Levi back through the original point-constituent projection.
The twist is faithful and binary irreducible, agrees with the ordinary
adjoint on SL₃, and has a natural cubic-fixed space of order sixteen with
zero L-plus fixed kernel. A projective inner cubic still moves a vector.
There is no binary equivalence with the ordinary projective adjoint.

Thus faithfulness and binary irreducibility do not repair the extension
selection step, even together with the fixed quotient and movement proved
for the selected chief section. This is a countermodel to that local
selection interface, not an identification of the original W or a
counterexample to the full ambient theorem. Every L-plus constituent on W,
the full parabolic chief-factor profile of this twist, its ambient exclusion,
the other centralizer branch, common-normal existence and both triangle
orientations remain to be established.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, B.4.14,
printed p.98, and the appeal to it in 11.1.2, printed pp.763--764.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
open Representation.SL3.AdjointCubicCentralizer

include m in
/-- Faithfulness, binary irreducibility, the restricted adjoint action, a
natural cubic-fixed quotient and surviving inner-cubic movement do not
select the ordinary extension. The countermodel uses the original field
and the literal L-plus quotient marking. It does not identify the original
chief section with this model or prove the full B.4.14 parabolic profile. -/
theorem linear_point_twisted_countermodel
    (hd : S.field.degree = 2) {X : Subgroup G}
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((SL3.flag D S m).Li 0) : Subgroup G) = 3) :
    let f := SL3.flag D S m
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    let r := (pointConstituentProjection D S m).comp
      (inclusion (show H ≤ f.Li 0 from (localResidual_le E).trans inf_le_left))
    letI : Algebra (ZMod 2) S.field.Carrier := ZMod.algebra S.field.Carrier 2
    ∃ hF : Nat.card S.field.Carrier = 4,
    ∃ ω : S.field.Carrierˣ, (ω : S.field.Carrier) ≠ 1 ∧
      orderOf (ProjGenLinGroup.mk (diagonalUnit S.field.Carrier ω)) = 3 ∧
      Representation.IsIrreducible (binaryTwistedAdjoint S.field.Carrier hF) ∧
      Function.Injective (binaryTwistedAdjoint S.field.Carrier hF) ∧
      (binaryTwistedAdjoint S.field.Carrier hF).comp SpecialLinearGroup.toPGL =
        (restrictScalars (k := ZMod 2) (projectiveAdjoint S.field.Carrier)).comp
          SpecialLinearGroup.toPGL ∧
      ¬ Nonempty ((restrictScalars (k := ZMod 2) (projectiveAdjoint S.field.Carrier)).Equiv
        (binaryTwistedAdjoint S.field.Carrier hF)) ∧
      (let hc := units_cube_of_card_four S.field.Carrier hF
       let C := twistedCubicFixed S.field.Carrier hc ω
       Nat.card C = 16 ∧
       ∃ e : C ≃ₗ[S.field.Carrier] (Fin 2 → S.field.Carrier),
         (∀ (h : H) (u : C), ∃ v : C,
           v.val = projectiveTwistedAdjoint S.field.Carrier hc
             (projectiveLevi S.field.Carrier (r h)) u.val ∧
           e v = (r h).val *ᵥ e u) ∧
         (∀ u : C,
           (∀ h : H, projectiveTwistedAdjoint S.field.Carrier hc
             (projectiveLevi S.field.Carrier (r h)) u.val = u.val) → u = 0) ∧
         ∃ h : H, orderOf (projectiveLevi S.field.Carrier (r h)) = 3 ∧
           ∃ u : C, projectiveTwistedAdjoint S.field.Carrier hc
             (projectiveLevi S.field.Carrier (r h)) u.val ≠ u.val) := by
  intro f E H r
  have hF : Nat.card S.field.Carrier = 4 := by rw [S.field.card_eq,hd]; decide
  let F := S.field.Carrier
  have hr : Function.Surjective r := linear_point_cubic_constituent_surjective D S m hcard
  let : Algebra (ZMod 2) S.field.Carrier := ZMod.algebra S.field.Carrier 2
  let : Fintype Fˣ := Fintype.ofFinite Fˣ
  have : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [←Nat.card_eq_fintype_card,Nat.card_units,hF]
    decide)
  obtain ⟨ω,hω⟩ := exists_ne (1 : Fˣ)
  have hω' : (ω : F) ≠ 1 := fun h => hω (Units.ext h)
  let hc := units_cube_of_card_four F hF
  have hω2 := square_ne_one_of_cube F ω hω' (congrArg Units.val (hc ω))
  refine ⟨hF,ω,hω',projective_diagonal_order F hF ω hω',
    binaryTwistedAdjoint_irreducible F hF,binaryTwistedAdjoint_injective F hF,
    binaryTwistedAdjoint_restriction F hF,binaryTwistedAdjoint_not_equivalent F hF ω hω',
    twistedCubicFixed_card F hF ω hω',twistedCubicCoordinates F hc ω hω' hω2,?_,?_,?_⟩
  · intro h u
    exact twistedCubicCoordinates_action F hc ω hω' hω2 (r h) u
  · intro u hu
    apply twistedCubicFixed_levi_fixed_eq_zero F hc ω hω' hω2 u
    intro g
    obtain ⟨h,rfl⟩ := hr g
    exact hu h
  · obtain ⟨g,hg,u,hu⟩ := twistedCubicFixed_inner_movement F hF ω hω'
    obtain ⟨h,rfl⟩ := hr g
    exact ⟨h,hg,u,hu⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
