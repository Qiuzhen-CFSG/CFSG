module

public import Theory.Representation.BinaryPermutation.CubicFixedSpace
public import Theory.Representation.SymplecticNatural
public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# A cubic fixed-space witness in the binary symplectic four-space

Use the existing polar representation of S₆, whose actual intertwining
map labels the fifteen nonzero vectors by duads. The regular Klein four
on four letters has only the remaining duad as a fixed duad, and the
three-cycle on the first three letters fixes it. This is a calculation
in the existing symplectic model; no identification of two A₆-actions
is inferred from their dimension or group name.

The alternating polar map lands in the actual derived symplectic group,
because A₆ is the commutator subgroup of S₆. Thus the witness applies to
both natural symplectic actions appearing in Aschbacher–Smith B.4.2,
B.5.1, and the comparison on p.1163 in Lemma 15.4.18.
-/

public section
open scoped Matrix
namespace Representation.SymplecticCubicFixedSpace
open BinaryOffender BinaryPermutation.CubicFixedSpace
open Theory.SpecificGroups.SymmetricSix

/-- The existing polar action restricted to the six-letter alternating group. -/
@[expose] noncomputable def alternatingPolar :
    Representation (ZMod 2) (alternatingGroup (Fin 6)) NaturalModule :=
  (symplecticNatural 2).comp (polarRepresentation.comp (alternatingGroup (Fin 6)).subtype)

private theorem duad_test (t : Duad)
    (h₁ : (first 6 (by decide)).val • t = t)
    (h₂ : (second 6 (by decide)).val • t = t) :
    (cycle 6 (by decide)).val • t = t := by
  apply duadSet_injective
  rw [duadSet_smul]
  have hc : ∀ t : Duad,
      (duadSet t).image (first 6 (by decide)).val = duadSet t →
      (duadSet t).image (second 6 (by decide)).val = duadSet t →
      (duadSet t).image (cycle 6 (by decide)).val = duadSet t := by decide +kernel
  apply hc t
  · simpa only [duadSet_smul] using congrArg duadSet h₁
  · simpa only [duadSet_smul] using congrArg duadSet h₂

/-- The cubic element fixes the Klein-fixed space in the actual matrix action. -/
theorem cycle_fixes_polar :
    ∀ v ∈ fixedSpace alternatingPolar (klein 6 (by decide)),
      alternatingPolar (cycle 6 (by decide)) v = v := by
  intro v hv
  by_cases hz : v = 0
  · subst v
    exact map_zero _
  obtain ⟨t, ht⟩ := polarVector_bijective.surjective (⟨v, hz⟩ : BinaryPoint)
  have ht' : (polarVector t).val = v := congrArg Subtype.val ht
  have hduad (a : alternatingGroup (Fin 6)) (ha : a ∈ klein 6 (by decide)) :
      a.val • t = t := by
    apply polarVector_injective
    apply Subtype.ext
    rw [← polarRepresentation_equivariant, ht']
    exact hv ⟨a, ha⟩
  have hc := duad_test t
    (hduad _ (first_mem 6 (by decide))) (hduad _ (second_mem 6 (by decide)))
  change (polarRepresentation (cycle 6 (by decide)).val).val *ᵥ v = v
  rw [← ht', polarRepresentation_equivariant, hc]

/-- The polar embedding of A₆ into the actual commutator subgroup Sp₄(2)'. -/
@[expose] noncomputable def alternatingDerivedPolar :
    alternatingGroup (Fin 6) →* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) :=
  (polarRepresentation.comp (alternatingGroup (Fin 6)).subtype).codRestrict _ (by
    intro g
    have hg : g.val ∈ commutator S6 := by
      rw [alternatingGroup.commutator_perm_eq (by norm_num [Letter])]
      exact g.property
    have hm : (commutator S6).map polarRepresentation ≤
        commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) := by
      rw [map_commutator_eq, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hm ⟨g.val, hg, rfl⟩)

theorem alternatingDerivedPolar_injective : Function.Injective alternatingDerivedPolar := by
  intro g h he
  apply Subtype.ext
  exact polarRepresentation_injective (congrArg Subtype.val he)

theorem symplectic_enlargement (S : Sylow 2 (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    ∃ d : Matrix.symplecticGroup (Fin 2) (ZMod 2), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (symplecticNatural 2) (S : Subgroup _),
        symplecticNatural 2 d v = v :=
  sylow_fixedSpace_enlargement_of_embedded_cubic (symplecticNatural 2)
    (polarRepresentation.comp (alternatingGroup (Fin 6)).subtype)
    (polarRepresentation_injective.comp Subtype.val_injective)
    _ (klein_isPGroup 6 (by decide)) _ (cycle_pow 6 (by decide))
    (cycle_ne_one 6 (by decide)) cycle_fixes_polar S

theorem symplecticDerived_enlargement
    (S : Sylow 2 (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) :
    ∃ d : commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (symplecticDerivedNatural 2) (S : Subgroup _),
        symplecticDerivedNatural 2 d v = v :=
  sylow_fixedSpace_enlargement_of_embedded_cubic (symplecticDerivedNatural 2) alternatingDerivedPolar
    alternatingDerivedPolar_injective _ (klein_isPGroup 6 (by decide)) _
    (cycle_pow 6 (by decide)) (cycle_ne_one 6 (by decide)) cycle_fixes_polar S

end Representation.SymplecticCubicFixedSpace
