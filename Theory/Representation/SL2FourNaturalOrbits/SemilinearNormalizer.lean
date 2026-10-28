module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Normalizer
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FixedSpaces
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FiveLines
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FieldDescent

/-!
# The semilinear normalizer of the binary natural SL₂(4) module

The faithful matrix-semilinear action identifies the full binary normalizer.
Its determinant-label action is the full S₃ with kernel SL₂. The specified
SL₂–Frobenius subgroup is S₅ through its faithful action on the five F₄-lines,
with SL₂ mapping to A₅ and coordinate Frobenius to a transposition. Its label
orbits have lengths one and two, whereas the full normalizer is transitive.

Every involution outside SL₂ in the normalizer is conjugate to coordinate
Frobenius by an F₄-linear map, and its fixed space has four elements. Within
the specified S₅ subgroup the conjugator can be chosen in SL₂. The descent
proof constructs an invariant basis from the matrix cocycle.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 6.2.5,
printed pp.680--681 (PDF pp.697--698). These are the concrete normalizer and
field-involution inputs; the plane-orbit classification and ambient fusion
conclusions remain with their source assembly.
-/

public section

noncomputable section
namespace Representation.SL2FourNatural.SemilinearNormalizer

/-- The actual normalizer acts on nonzero wedge values by its label permutation. -/
theorem normalizerLabels_wedge (x : normalizer) (u v : V) (a : Fˣ)
    (ha : wedge u v = (a : F)) :
    wedge (x.val u) (x.val v) = (normalizerLabels x a : F) := by
  obtain ⟨g, rfl⟩ := normalizerEquiv.surjective x
  rw [normalizerEquiv_apply, wedge_natural, ha, normalizerLabels_equiv, labels_apply]

/-- The full binary normalizer is transitive on the three determinant labels. -/
theorem normalizerLabels_transitive (a b : Fˣ) :
    ∃ x : normalizer, normalizerLabels x a = b := by
  obtain ⟨g, hg⟩ := labels_transitive a b
  exact ⟨normalizerEquiv g, by simpa only [normalizerLabels_equiv] using hg⟩

/-- The specified binary S₅ fixes the determinant label one. -/
theorem specialFieldLabels_fixes_one (x : specialField) :
    specialFieldLabels x 1 = 1 :=
  specialFieldGamma_fixes_one (specialFieldEquiv.symm x)

/-- The label orbit lengths for the literal binary S₅ are one and two. -/
theorem specialField_orbit_card (a : Fˣ) :
    Nat.card {b : Fˣ // ∃ x : specialField, specialFieldLabels x a = b} =
      if a = 1 then 1 else 2 := by
  have e : {b : Fˣ // ∃ x : specialField, specialFieldLabels x a = b} ≃
      {b : Fˣ // ∃ g : specialFieldGamma, labels g.val a = b} :=
    Equiv.subtypeEquivRight (fun b =>
      (specialField_label_orbit a b).trans (specialFieldGamma_label_orbit a b).symm)
  rw [Nat.card_congr e, specialFieldGamma_orbit_card]

/-- Outer involutions in the full binary normalizer fix GL₂-translates of the
coordinate field plane, with the original natural action as transporter. -/
theorem normalizer_involution_fixed_space (x : BinaryGL) (hx : x ∈ normalizer)
    (h2 : x ^ 2 = 1) (hSL : x ∉ action.range) :
    ∃ B : LinearGroup,
      x.toLinearMap.fixedSubmodule = fieldFixed.map (linear B).toLinearMap := by
  obtain ⟨B, rfl⟩ := normalizer_involution_conjugate x hx h2 hSL
  exact ⟨B, conjugate_fieldFixed (linear B)⟩

/-- In the specified binary S₅ every outer involution fixes an SL₂-translate
of the coordinate field plane. This supplies the field-type orbit input. -/
theorem specialField_involution_fixed_space (x : BinaryGL) (hx : x ∈ specialField)
    (h2 : x ^ 2 = 1) (hSL : x ∉ action.range) :
    ∃ A : SL,
      x.toLinearMap.fixedSubmodule = fieldFixed.map (action A).toLinearMap := by
  obtain ⟨A, rfl⟩ := specialField_involution_conjugate x hx h2 hSL
  exact ⟨A, conjugate_fieldFixed (action A)⟩

end Representation.SL2FourNatural.SemilinearNormalizer
