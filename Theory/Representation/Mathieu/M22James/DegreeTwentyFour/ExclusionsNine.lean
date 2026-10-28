module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Reduction
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Nonsimple
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Simple

/-!
# Assembly of the central degree-nine exclusion

Restrict the centrally marked F₄ action to F₂. Scalar stability preserves
irreducibility and faithfulness, and the tower formula gives binary dimension
eighteen. The conjugate-pair trace argument rules out every nonsimple point
restriction, including all nonsplit extensions. An actual simple point module
is equivalent to one of the two mixed tensor models, and the checked matrix
obstructions rule out extension of either model to the full cover. These two
branches prove the degree-nine exclusion without additional premises.

Source context: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, pp.15–16 and Theorem 6.6/Table 6.7. The latter source's
representation degree list is not assumed in this module.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
open Representation Uniqueness.PointRestriction

universe u

/-- The nonsimple branch and scalar restriction are discharged. Only the explicit
simple-point extension obstruction remains for final degree-nine assembly. -/
theorem centralFieldDegreeExclusion_nine_of_simple_point_exclusion
    (hex : ExclusionsNine.SimplePointExtensionExclusion.{u}) :
    CentralFieldDegreeExclusion.{u} 9 := by
  intro W _ _ _ τ hf hi hs hd
  let := hi
  let : Module (ZMod 2) W := Module.compHom W (algebraMap (ZMod 2) F)
  let : FiniteDimensional (ZMod 2) W := Module.Finite.trans F W
  let ρ : Representation (ZMod 2) M22TripleCover W := restrictScalars τ
  have hirr : ρ.IsIrreducible := ExclusionsNine.restrictScalars_isIrreducible τ hs
  let := hirr
  have hfaith : Function.Injective ρ := ExclusionsNine.restrictScalars_faithful τ hf
  have hdim : Module.finrank (ZMod 2) W = 18 := by
    rw [← Module.finrank_mul_finrank (ZMod 2) F W, QuadraticAlgebra.finrank_eq_two, hd]
  exact hex W ρ (pointAction_centralQuadratic ρ hfaith)
    (ExclusionsNine.pointAction_isIrreducible_of_finrank_eighteen ρ hfaith hdim) hdim

/-- No faithful irreducible F₄ action of the actual triple Mathieu cover with
the specified central scalar has dimension nine. Both point-restriction
branches are discharged, without assuming absolute irreducibility or a
representation degree catalogue. -/
theorem centralFieldDegreeExclusion_nine : CentralFieldDegreeExclusion.{u} 9 :=
  centralFieldDegreeExclusion_nine_of_simple_point_exclusion
    ExclusionsNine.simplePointExtensionExclusion

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
