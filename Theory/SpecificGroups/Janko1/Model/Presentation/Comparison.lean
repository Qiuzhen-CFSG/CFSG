module

public import Theory.SpecificGroups.Janko1.Model.Certification
public import Theory.SpecificGroups.Janko1.Model.Presentation

/-!
# Comparison through the full ATLAS presentation of J₁

A nontrivial pair satisfying all five ATLAS relators defines a homomorphism
from `AtlasPresentation`. If that presentation is finite of order at most
175560, its existing surjection onto the certified matrix model is bijective.
The resulting map from the simple matrix model is injective whenever the
first element of the pair is nonidentity. If the receiving group also has
order 175560, this gives a multiplicative equivalence, with the first element
sent to the standard matrix involution.

The presentation bound is an explicit, unproved premise here. The concrete
matrix order certificate does not bound the presented group: its equalities
are checked in matrices, not derived in the presented group. The source-side
existence of a nontrivial pair is another independent premise. Neither this
module nor the existing presentation surjection proves Janko's recognition
theorem without those premises.

Source for the five relators: ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J1G1-P1
(inspected 8 October 2026). The source application is Aschbacher–Smith I.4.9,
printed p.418, which cites Janko, J. Algebra 3 (1966), 147–186.
-/

namespace Janko1

private theorem map_atlas_word {H K : Type*} [Group H] [Group K]
    (f : H →* K) (x y : H) (i : Fin 5) :
    f (atlasWord x y i) = atlasWord (f x) (f y) i := by
  fin_cases i <;> simp [atlasWord]

/-- Evaluate the literal presented-group generators at a pair satisfying all five relators. -/
public def atlasPairHom {H : Type*} [Group H] (x y : H)
    (hrel : ∀ i, atlasWord x y i = 1) : AtlasPresentation →* H :=
  PresentedGroup.toGroup (f := fun i => if i then y else x) (by
    rintro _ ⟨i, rfl⟩
    rw [atlasRelator, map_atlas_word, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    exact hrel i)

/-- The first presented generator evaluates to the first element of the pair. -/
@[simp] public theorem atlasPairHom_false {H : Type*} [Group H] (x y : H)
    (hrel : ∀ i, atlasWord x y i = 1) :
    atlasPairHom x y hrel (presentationGenerator false) = x :=
  PresentedGroup.toGroup.of _

/-- The second presented generator evaluates to the second element of the pair. -/
@[simp] public theorem atlasPairHom_true {H : Type*} [Group H] (x y : H)
    (hrel : ∀ i, atlasWord x y i = 1) :
    atlasPairHom x y hrel (presentationGenerator true) = y :=
  PresentedGroup.toGroup.of _

/-- A finite upper bound on the presentation makes the existing model surjection bijective. -/
public theorem presentationToModel_bijective_of_bound
    (hbound : Finite AtlasPresentation ∧ Nat.card AtlasPresentation ≤ 175560) :
    Function.Bijective presentationToModel := by
  let := hbound.1
  exact presentationToModel_surjective.bijective_of_nat_card_le (by
    rw [card_model]
    exact hbound.2)

/-- The canonical equivalence to the model, conditional on the presentation bound. -/
public noncomputable def presentationEquivModelOfBound
    (hbound : Finite AtlasPresentation ∧ Nat.card AtlasPresentation ≤ 175560) :
    AtlasPresentation ≃* Model :=
  MulEquiv.ofBijective presentationToModel (presentationToModel_bijective_of_bound hbound)

/-- The conditional presentation equivalence preserves the specified generators. -/
@[simp] public theorem presentationEquivModelOfBound_generator
    (hbound : Finite AtlasPresentation ∧ Nat.card AtlasPresentation ≤ 175560) (i : Bool) :
    presentationEquivModelOfBound hbound (presentationGenerator i) = modelGenerator i :=
  presentationToModel_generator i

/-- Descend a relator pair to a homomorphism from the actual matrix model. -/
public noncomputable def modelHomOfAtlasPair {H : Type*} [Group H]
    (hbound : Finite AtlasPresentation ∧ Nat.card AtlasPresentation ≤ 175560)
    (x y : H) (hrel : ∀ i, atlasWord x y i = 1) : Model →* H :=
  (atlasPairHom x y hrel).comp (presentationEquivModelOfBound hbound).symm.toMonoidHom

/-- The comparison homomorphism sends the standard involution to the first element. -/
@[simp] public theorem modelHomOfAtlasPair_a {H : Type*} [Group H]
    (hbound : Finite AtlasPresentation ∧ Nat.card AtlasPresentation ≤ 175560)
    (x y : H) (hrel : ∀ i, atlasWord x y i = 1) :
    modelHomOfAtlasPair hbound x y hrel a = x := by
  have he : (presentationEquivModelOfBound hbound).symm a = presentationGenerator false :=
    (presentationEquivModelOfBound hbound).symm_apply_eq.mpr
      (presentationToModel_generator false).symm
  change atlasPairHom x y hrel ((presentationEquivModelOfBound hbound).symm a) = x
  rw [he, atlasPairHom_false]

/-- The comparison homomorphism sends the standard element of order three to the second element. -/
@[simp] public theorem modelHomOfAtlasPair_b {H : Type*} [Group H]
    (hbound : Finite AtlasPresentation ∧ Nat.card AtlasPresentation ≤ 175560)
    (x y : H) (hrel : ∀ i, atlasWord x y i = 1) :
    modelHomOfAtlasPair hbound x y hrel b = y := by
  have he : (presentationEquivModelOfBound hbound).symm b = presentationGenerator true :=
    (presentationEquivModelOfBound hbound).symm_apply_eq.mpr
      (presentationToModel_generator true).symm
  change atlasPairHom x y hrel ((presentationEquivModelOfBound hbound).symm b) = y
  rw [he, atlasPairHom_true]

/-- Model simplicity makes a nontrivial comparison map injective; pair generation is unnecessary. -/
public theorem modelHomOfAtlasPair_injective {H : Type*} [Group H]
    (hbound : Finite AtlasPresentation ∧ Nat.card AtlasPresentation ≤ 175560)
    (x y : H) (hx : x ≠ 1) (hrel : ∀ i, atlasWord x y i = 1) :
    Function.Injective (modelHomOfAtlasPair hbound x y hrel) := by
  let f := modelHomOfAtlasPair hbound x y hrel
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact (MonoidHom.ker_eq_bot_iff f).mp hbot
  · have ha : a ∈ f.ker := by rw [htop]; trivial
    have he := MonoidHom.mem_ker.mp ha
    exact (hx ((modelHomOfAtlasPair_a hbound x y hrel).symm.trans he)).elim

/-- Recognition from a nontrivial relator pair and a finite presentation bound. -/
public noncomputable def equivModelOfAtlasPair {H : Type*} [Group H] [Finite H]
    (hbound : Finite AtlasPresentation ∧ Nat.card AtlasPresentation ≤ 175560)
    (horder : Nat.card H = 175560) (x y : H) (hx : x ≠ 1)
    (hrel : ∀ i, atlasWord x y i = 1) : H ≃* Model :=
  (MulEquiv.ofBijective (modelHomOfAtlasPair hbound x y hrel)
    ((modelHomOfAtlasPair_injective hbound x y hx hrel).bijective_of_nat_card_le
      (by rw [horder, card_model]))).symm

/-- The resulting equivalence marks the first element by the standard matrix involution. -/
@[simp] public theorem equivModelOfAtlasPair_x {H : Type*} [Group H] [Finite H]
    (hbound : Finite AtlasPresentation ∧ Nat.card AtlasPresentation ≤ 175560)
    (horder : Nat.card H = 175560) (x y : H) (hx : x ≠ 1)
    (hrel : ∀ i, atlasWord x y i = 1) :
    equivModelOfAtlasPair hbound horder x y hx hrel x = a := by
  exact (MulEquiv.symm_apply_eq _).mpr (modelHomOfAtlasPair_a hbound x y hrel).symm

/-- Simultaneous conjugation preserves the five literal ATLAS relators. -/
public theorem atlas_relations_conj {H : Type*} [Group H] (x y g : H)
    (hrel : ∀ i, atlasWord x y i = 1) :
    ∀ i, atlasWord (g * x * g⁻¹) (g * y * g⁻¹) i = 1 := by
  intro i
  have he := congrArg (MulAut.conj g).toMonoidHom (hrel i)
  rw [map_atlas_word, map_one] at he
  exact he

end Janko1
