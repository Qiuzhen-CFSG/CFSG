module
public import Theory.SpecificGroups.Triality.OddSupplement
public import Theory.SpecificGroups.Triality.ElementarySylowFixers
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Maximal Sylow-center centralizers in binary triality

The arms parabolic normalizes the center of its root radical, which is the
center of the full positive Sylow subgroup. At q = 2 that center has order
two, so the parabolic centralizes it. The proved parabolic maximality and
ambient centerlessness identify the full centralizer. Sylow conjugacy
retains the caller's original marking under any actual model equivalence.

Source: Aschbacher--Smith 15.1.20(3c), printed p.1096; the genuine
triality root geometry and automorphism results are cited in the imports.
-/

public section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.SylowCenterMaximal
open Parabolics

private theorem standard_normalizes :
    parabolic (binaryParameters 1 Nat.zero_lt_one) .arms ≤ normalizer
      ((center (unipotent (binaryParameters 1 Nat.zero_lt_one))).map
        (unipotent (binaryParameters 1 Nat.zero_lt_one)).subtype :
          Set (BinaryCarrier 1 Nat.zero_lt_one)) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  rw [← RadicalCoordinates.embedded_center_radical_arms_eq_center_unipotent P rfl]
  exact ((normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P .arms)).mp
    inferInstance).trans (normalizer_le_normalizer_characteristic_image
      (radical P .arms) (center (radical P .arms)))

theorem standard_centralizer_isCoatom : IsCoatom (centralizer
    ((center (unipotent (binaryParameters 1 Nat.zero_lt_one))).map
      (unipotent (binaryParameters 1 Nat.zero_lt_one)).subtype :
        Set (BinaryCarrier 1 Nat.zero_lt_one))) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let Z := (center (unipotent P)).map (unipotent P).subtype
  have hz : Nat.card Z = 2 := by
    rw [card_map_of_injective (unipotent P).subtype_injective]
    simpa [P, Parameters.q, binaryParameters] using
      RadicalCoordinates.Centers.card_center_unipotent P rfl
  have hle : parabolic P .arms ≤ centralizer (Z : Set (Carrier P)) :=
    standard_normalizes.trans (normalizer_le_centralizer_of_card_two Z hz)
  have hne : centralizer (Z : Set (Carrier P)) ≠ ⊤ := by
    intro he
    have hZ : Z = ⊥ := bot_unique (by
      rw [← binaryCarrier_center_eq_bot 1 Nat.zero_lt_one]
      exact centralizer_eq_top_iff_subset.mp he)
    rw [hZ, card_bot] at hz
    omega
  have he := ((OddSupplement.parabolic_isCoatom 1 Nat.zero_lt_one .arms).le_iff_eq hne).mp hle
  rw [he]
  exact OddSupplement.parabolic_isCoatom 1 Nat.zero_lt_one .arms

private theorem centralizer_map_equiv {K H : Type*} [Group K] [Group H]
    (e : K ≃* H) (Z : Subgroup K) :
    (centralizer (Z : Set K)).map e.toMonoidHom = centralizer (Z.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro z hz
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e z) (mem_map_of_mem _ hz)

/-- Maximality for any actual binary triality model and the caller's Sylow. -/
theorem centralizer_isCoatom {K : Type*} [Group K]
    (e : K ≃* BinaryCarrier 1 Nat.zero_lt_one) (S : Sylow 2 K) :
    IsCoatom (centralizer ((center S).map (S : Subgroup K).subtype : Set K)) := by
  let : Finite K := Finite.of_injective e e.injective
  let P := binaryParameters 1 Nat.zero_lt_one
  obtain ⟨_,f,_,hf⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    e S (unipotentSylow P rfl)
  change (S : Subgroup K).map f.toMonoidHom = unipotent P at hf
  have hZ : ((center S).map (S : Subgroup K).subtype).map f.toMonoidHom =
      (center (unipotent P)).map (unipotent P).subtype := by
    rw [map_map, ← map_center_image_of_injective (S : Subgroup K) f.toMonoidHom f.injective, hf]
  apply (f.mapSubgroup.isCoatom_iff _).mp
  change IsCoatom ((centralizer ((center S).map (S : Subgroup K).subtype : Set K)).map f.toMonoidHom)
  rw [centralizer_map_equiv, hZ]
  exact standard_centralizer_isCoatom

end Triality.Standard.SylowCenterMaximal
