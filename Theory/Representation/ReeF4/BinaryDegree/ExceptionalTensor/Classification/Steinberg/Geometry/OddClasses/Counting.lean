module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.SourceCoordinates
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.ReflectionLifts
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.Lang
/-!
# Counting the original finite Ree odd-order classes

Choose a torus representative for each odd-order conjugacy class of the
literal finite model. Its four fundamental orbit sums form two compatible
Frobenius pairs. Equality of these codes gives an actual Weyl relation and
hence an ambient conjugator. The proved Lang correction descends this
conjugator when the original point centralizer is connected. The resulting
injection has a target of cardinality q², exactly the number of restricted
binary weights. No character-separation or torus-placement premise remains.

Source: Steinberg (1963), §§3.9 and 12.2, with centralizer Lang correction.
Semisimple F4 centralizer connectedness is the explicit independent geometric
input retained by the final endpoint.
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses
open F4WeightAction
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

noncomputable local instance countingTorusGroup : AlgebraicGroup (F4Chevalley.splitTorus (k:=F)).carrierVariety :=
  (F4Chevalley.splitTorus (k:=F)).carrierAlgebraicGroup
open scoped F4WeightAction
lemma corootTorus_isConj_of_fundamentalValues_eq (t s : Fin 4 → Fˣ)
    (heq : ∀ i : Fin 4, fundamentalValue t i = fundamentalValue s i) :
    IsConj (corootTorusElement t) (corootTorusElement s) := by
  obtain ⟨w, hw⟩ := exists_weyl_of_fundamentalValue_eq t s heq
  have he : ∀ a : F4WeightAction.Weight,
      (RootModel.Corrected.leftCharacter a).pointCharacter (corootPoint s) =
      (RootModel.Corrected.leftCharacter (representation w a)).pointCharacter (corootPoint t) := by
    intro a
    rw [leftCharacter_corootPoint, leftCharacter_corootPoint]
    exact congrArg Units.val (hw (Multiplicative.ofAdd a))
  have h := SemisimpleCentralizers.ambient_isConj_of_weyl_leftCharacter
    (corootPoint t) (corootPoint s) w he
  simpa only [corootPoint_inclusion] using h

private theorem class_bound_of_toral_separation_and_fusion (m : ℕ) (f : CoefficientField m →+* F)
    (htoral : ∀ t s : Fin 4 → Fˣ, (∀ i : Fin 4, fundamentalValue t i = fundamentalValue s i) →
      IsConj (corootTorusElement t) (corootTorusElement s))
    (hfusion : ∀ x y : Model m, (¬ 2 ∣ orderOf x) → (¬ 2 ∣ orderOf y) →
      IsConj (modelEmbedding f x) (modelEmbedding f y) → IsConj x y) :
    Nat.card (ConjClasses.mk '' {g : Model m | ¬ 2 ∣ orderOf g}) ≤ Nat.card (RestrictedWeight m) := by
  classical
  let C := ConjClasses.mk '' {g : Model m | ¬ 2 ∣ orderOf g}
  let r : C → Model m := fun z => Classical.choose z.property
  have hr (z : C) : (¬ 2 ∣ orderOf (r z)) ∧ ConjClasses.mk (r z) = z.val :=
    Classical.choose_spec z.property
  have hp (z : C) : ∃ a : PointGroup F × (Fin 4 → Fˣ),
      modelEmbedding f (r z) = a.1 * corootTorusElement a.2 * a.1⁻¹ := by
    obtain ⟨c,t,h⟩ := model_exists_coroot_conjugate f (r z) (hr z).1
    exact ⟨(c,t),h⟩
  let a (z : C) := Classical.choose (hp z)
  have ha (z : C) : modelEmbedding f (r z) = (a z).1 * corootTorusElement (a z).2 * (a z).1⁻¹ :=
    Classical.choose_spec (hp z)
  let e := SourceFixedPoints.modelEquiv m f
  let code (z : C) : CoordinateCount.TwistedPair m F × CoordinateCount.TwistedPair m F :=
    fixedCoordinateCode m (e (r z)) (a z).1 (a z).2 (ha z)
  have hcode : Function.Injective code := by
    intro x y h
    have hv := (fixedCoordinateCode_eq_iff m (e (r x)) (e (r y))
      (a x).1 (a y).1 (a x).2 (a y).2 (ha x) (ha y)).mp h
    have hxy := htoral (a x).2 (a y).2 hv
    have hx : IsConj (corootTorusElement (a x).2) (modelEmbedding f (r x)) :=
      isConj_iff.mpr ⟨(a x).1,(ha x).symm⟩
    have hy : IsConj (corootTorusElement (a y).2) (modelEmbedding f (r y)) :=
      isConj_iff.mpr ⟨(a y).1,(ha y).symm⟩
    have hc := hfusion (r x) (r y) (hr x).1 (hr y).1 (hx.symm.trans (hxy.trans hy))
    apply Subtype.ext
    rw [← (hr x).2, ← (hr y).2]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr hc
  let _ := CoordinateCount.finite_twistedPair m f
  exact (Nat.card_le_card_of_injective code hcode).trans_eq (CoordinateCount.card_coordinate_pairs m f)
theorem model_odd_class_bound_of_fusion (m : ℕ) (f : CoefficientField m →+* F)
    (hfusion : ∀ x y : Model m, (¬ 2 ∣ orderOf x) → (¬ 2 ∣ orderOf y) →
      IsConj (modelEmbedding f x) (modelEmbedding f y) → IsConj x y) :
    Nat.card (ConjClasses.mk '' {g : Model m | ¬ 2 ∣ orderOf g}) ≤ Nat.card (RestrictedWeight m) :=
  class_bound_of_toral_separation_and_fusion m f corootTorus_isConj_of_fundamentalValues_eq hfusion

theorem model_odd_class_bound_of_connected_centralizers (m : ℕ) (f : CoefficientField m →+* F)
    (hconnected : ∀ x : Model m, (¬ 2 ∣ orderOf x) →
      Variety.IsConnected (SemisimpleCentralizers.pointCentralizer (modelEmbedding f x)).carrierVariety) :
    Nat.card (ConjClasses.mk '' {g : Model m | ¬ 2 ∣ orderOf g}) ≤ Nat.card (RestrictedWeight m) := by
  apply model_odd_class_bound_of_fusion m f
  intro x y hx _ hxy
  exact SemisimpleCentralizers.isConj_model_of_connected_centralizer m f x y (hconnected x hx) hxy

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses
