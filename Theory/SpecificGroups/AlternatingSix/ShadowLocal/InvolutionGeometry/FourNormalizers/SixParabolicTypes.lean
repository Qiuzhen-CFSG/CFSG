module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.SixParabolicCoordinates

/-!
# Four-group classes are the two source parabolic types

The full automorphism normalizers are the natural images of the compatible
conjugate duad and syntheme stabilizers. Their alternating parts are not
inner-conjugate: two explicit elements of the syntheme normalizer have no
common invariant duad. The classification of four-groups into two inner
classes then identifies the natural S₆ with the automorphisms preserving
both literal parabolic types. All finite tests use kernel reduction.

Source: Aschbacher–Smith, I.5, printed pp.419–422, and 13.8.21(2),
printed p.956 (PDF p.973). This is intrinsic diagram geometry and uses
no representation-theoretic exclusion.
-/

@[expose] public section

open Subgroup AlternatingSix.ShadowLocal AlternatingSix.ShadowLocal.FourNormalizers
open AlternatingSix.ShadowLocal.FourNormalizers.SixParabolics
open Theory.SpecificGroups.SymmetricSix hiding A6
namespace AlternatingSix.ShadowLocal.FourNormalizers.SixParabolics
local instance : Fintype S6 := fintypePerm
local instance : Fintype A6 := Subtype.fintype _
local notation "N₁" => normalizer (standardFour : Set A6)
local notation "N₂" => normalizer (secondFour : Set A6)

theorem four_stabilizer_natural (F : Subgroup A6) [IsKleinFour F]
    (β : AutA6) (hβ : F.map β.toMonoidHom = F) : β ∈ natural := by
  obtain ⟨α, rfl⟩ := exists_map_standardFour F
  have hs : standardFour.map (α⁻¹ * β * α).toMonoidHom = standardFour := by
    apply Subgroup.map_injective (f := α.toMonoidHom) α.injective
    rw [map_map]
    have he : α.toMonoidHom.comp (α⁻¹ * β * α).toMonoidHom =
        β.toMonoidHom.comp α.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact α.apply_symm_apply _
    rw [he, ← map_map]
    exact hβ
  have hn := (natural_conjugation_iff α (α⁻¹ * β * α)).mpr
    (standard_stabilizer_le_natural _ hs)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hn

theorem standard_aut_normalizer_coordinates :
    normalizer (standardFour.map (MulAut.conj : A6 →* AutA6) : Set AutA6) =
      ((MulAut.conj coordinates.val).mapSubgroup duadStabilizer).map permutationAction := by
  ext β
  rw [mem_inner_normalizer_iff]
  constructor
  · intro hb
    obtain ⟨σ, hσ⟩ := standard_stabilizer_le_natural β hb
    change permutationAction σ = β at hσ
    subst β
    refine ⟨σ, ?_, rfl⟩
    change σ ∈ duadStabilizer.map (MulAut.conj coordinates.val).toMonoidHom
    rw [mem_map_equiv]
    exact (standard_test σ).mp ((natural_stabilizes_standard_iff σ).mp hb)
  · rintro ⟨σ, hσ, rfl⟩
    apply (natural_stabilizes_standard_iff σ).mpr
    apply (standard_test σ).mpr
    exact (mem_map_equiv).mp hσ

theorem second_aut_normalizer_coordinates :
    normalizer (secondFour.map (MulAut.conj : A6 →* AutA6) : Set AutA6) =
      ((MulAut.conj coordinates.val).mapSubgroup synthemeStabilizer).map permutationAction := by
  ext β
  rw [mem_inner_normalizer_iff]
  constructor
  · intro hb
    obtain ⟨σ, hσ⟩ := four_stabilizer_natural secondFour β hb
    change permutationAction σ = β at hσ
    subst β
    refine ⟨σ, ?_, rfl⟩
    change σ ∈ synthemeStabilizer.map (MulAut.conj coordinates.val).toMonoidHom
    rw [mem_map_equiv]
    apply (second_test σ).mp
    have hh := (map_second_eq_iff _).mp hb
    simp only [Subtype.ext_iff] at hh
    exact hh
  · rintro ⟨σ, hσ, rfl⟩
    apply (map_second_eq_iff _).mpr
    simp only [Subtype.ext_iff]
    apply (second_test σ).mpr
    exact (mem_map_equiv).mp hσ

private def mover : Fin 2 → A6 :=
  ![dihedralReflection,
    ⟨Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 2 3 * Equiv.swap 3 5, by decide⟩]

private theorem mover_mem (i : Fin 2) : mover i ∈ N₂ := by
  rw [mem_normalizer_iff_map_conj_eq]
  change secondFour.map (MulAut.conj (mover i)).toMonoidHom = secondFour
  rw [map_second_eq_iff]
  simp only [Subtype.ext_iff]
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
private theorem no_common_commutation (g : S6) :
    ¬ ∀ i : Fin 2, (g⁻¹ * (mover i).val * g) * tailSwap =
      tailSwap * (g⁻¹ * (mover i).val * g) := by
  revert g
  decide +kernel

theorem second_normalizer_not_standard_conjugate :
    ¬ ∃ g : A6, N₂ = (N₁).map (MulAut.conj g).toMonoidHom := by
  rintro ⟨g, hg⟩
  apply no_common_commutation g.val
  intro i
  have hi := mover_mem i
  rw [hg, mem_map_equiv] at hi
  rw [mem_normalizer_iff_map_conj_eq, ← permutationAction_coe] at hi
  change standardFour.map (permutationAction _).toMonoidHom = standardFour at hi
  exact (natural_stabilizes_standard_iff _).mp hi

private theorem map_conjugate (F : Subgroup A6) (α : AutA6) (g : A6) :
    (F.map (MulAut.conj g).toMonoidHom).map α.toMonoidHom =
      (F.map α.toMonoidHom).map (MulAut.conj (α g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change α (g * x * g⁻¹) = α g * α x * (α g)⁻¹
  simp only [map_mul, map_inv]

theorem natural_iff_second_conjugate (β : AutA6) :
    β ∈ natural ↔ ∃ g : A6,
      secondFour.map β.toMonoidHom = secondFour.map (MulAut.conj g).toMonoidHom := by
  have transfer (α δ : AutA6) (F : Subgroup A6) :
      (F.map (α⁻¹ * δ * α).toMonoidHom).map α.toMonoidHom =
        (F.map α.toMonoidHom).map δ.toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact α.apply_symm_apply _
  constructor
  · intro hb
    have hc : classSwap⁻¹ * β * classSwap ∈ natural := by
      simpa only [inv_inv] using (natural_conjugation_iff classSwap⁻¹ β).mpr hb
    obtain ⟨g, hg⟩ := (natural_iff_standard_conjugate _).mp hc
    refine ⟨classSwap g, ?_⟩
    have he := congrArg (map classSwap.toMonoidHom) hg
    rw [transfer, map_conjugate, classSwap_standardFour] at he
    exact he
  · rintro ⟨g, hg⟩
    have hf : secondFour.map ((MulAut.conj g)⁻¹ * β).toMonoidHom = secondFour := by
      change secondFour.map ((MulAut.conj g).symm.toMonoidHom.comp β.toMonoidHom) = _
      rw [← map_map, hg, map_map]
      simp
    have hn := four_stabilizer_natural _ _ hf
    have hi : MulAut.conj g ∈ natural := inner_le_natural ⟨g, rfl⟩
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using natural.mul_mem hi hn

private theorem map_inner_comp (H : Subgroup A6) (g h : A6) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [map_map]
  congr 1

theorem natural_iff_standard_normalizer_conjugate (β : AutA6) :
    β ∈ natural ↔ ∃ g : A6, (N₁).map β.toMonoidHom =
      (N₁).map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro hb
    obtain ⟨g, hg⟩ := (natural_iff_standard_conjugate β).mp hb
    exact ⟨g, by rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq, hg]⟩
  · rintro ⟨g, hg⟩
    by_contra hb
    let F := standardFour.map β.toMonoidHom
    let e := standardFour.equivMapOfInjective β.toMonoidHom β.injective
    let : IsKleinFour F := {
      card_four := (Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans IsKleinFour.exponent_two }
    rcases four_has_two_classes F with ⟨h, hh⟩ | ⟨h, hh⟩
    · exact hb ((natural_iff_standard_conjugate β).mpr ⟨h, hh⟩)
    · have hn : (N₁).map β.toMonoidHom = (N₂).map (MulAut.conj h).toMonoidHom := by
        rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq]
        exact congrArg (fun H : Subgroup A6 => normalizer (H : Set A6)) hh
      have he := congrArg (map (MulAut.conj h⁻¹).toMonoidHom) (hn.symm.trans hg)
      rw [map_inner_comp, map_inner_comp, inv_mul_cancel] at he
      simp only [map_one] at he
      change (N₂).map (MonoidHom.id _) = _ at he
      rw [Subgroup.map_id] at he
      exact second_normalizer_not_standard_conjugate ⟨h⁻¹ * g, he⟩

theorem natural_iff_preserves_normalizer_types (β : AutA6) :
    β ∈ natural ↔
      (∃ g : A6, (N₁).map β.toMonoidHom = (N₁).map (MulAut.conj g).toMonoidHom) ∧
      (∃ g : A6, (N₂).map β.toMonoidHom = (N₂).map (MulAut.conj g).toMonoidHom) := by
  constructor
  · intro hb
    refine ⟨(natural_iff_standard_normalizer_conjugate β).mp hb, ?_⟩
    obtain ⟨g, hg⟩ := (natural_iff_second_conjugate β).mp hb
    exact ⟨g, by rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq, hg]⟩
  · exact fun h => (natural_iff_standard_normalizer_conjugate β).mpr h.1
private theorem class_coordinate_iff (H : Subgroup A6) (c : A6) (β : AutA6) :
    (∃ g : A6, (H.map (MulAut.conj c).toMonoidHom).map β.toMonoidHom =
      (H.map (MulAut.conj c).toMonoidHom).map (MulAut.conj g).toMonoidHom) ↔
    (∃ g : A6, H.map β.toMonoidHom = H.map (MulAut.conj g).toMonoidHom) := by
  constructor
  · rintro ⟨g, hg⟩
    rw [map_conjugate, map_inner_comp] at hg
    have he := congrArg (map (MulAut.conj (β c)⁻¹).toMonoidHom) hg
    rw [map_inner_comp, map_inner_comp, inv_mul_cancel] at he
    simp only [map_one] at he
    change (H.map β.toMonoidHom).map (MonoidHom.id _) = _ at he
    rw [Subgroup.map_id] at he
    exact ⟨(β c)⁻¹ * (g * c), he⟩
  · rintro ⟨g, hg⟩
    refine ⟨β c * g * c⁻¹, ?_⟩
    rw [map_conjugate, hg, map_inner_comp, map_inner_comp]
    simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Natural automorphisms are exactly the automorphisms preserving both
literal source parabolic types, each up to inner conjugacy. -/
theorem natural_iff_preserves_source_parabolic_types (β : AutA6) :
    β ∈ natural ↔
      (∃ g : A6, a6DuadStabilizer.map β.toMonoidHom =
        a6DuadStabilizer.map (MulAut.conj g).toMonoidHom) ∧
      (∃ g : A6, a6SynthemeStabilizer.map β.toMonoidHom =
        a6SynthemeStabilizer.map (MulAut.conj g).toMonoidHom) := by
  have h := natural_iff_preserves_normalizer_types β
  rw [standard_normalizer_coordinates, second_normalizer_coordinates] at h
  exact h.trans (and_congr (class_coordinate_iff _ _ _) (class_coordinate_iff _ _ _))
/-- Both marked normalizers use the same incident flag coordinates. -/
theorem normalizers_inf_coordinates :
    normalizer (standardFour : Set A6) ⊓ normalizer (secondFour : Set A6) =
      (MulAut.conj coordinates).mapSubgroup a6Borel := by
  rw [standard_normalizer_coordinates, second_normalizer_coordinates]
  exact ((MulAut.conj coordinates).mapSubgroup.map_inf
    a6DuadStabilizer a6SynthemeStabilizer).symm

/-- Preserving the two inner classes of four-groups is precisely
preserving the two actual source parabolic types. -/
theorem four_classes_iff_source_parabolic_types (β : AutA6) :
    ((∃ g : A6, standardFour.map β.toMonoidHom =
        standardFour.map (MulAut.conj g).toMonoidHom) ∧
      (∃ g : A6, secondFour.map β.toMonoidHom =
        secondFour.map (MulAut.conj g).toMonoidHom)) ↔
    ((∃ g : A6, a6DuadStabilizer.map β.toMonoidHom =
        a6DuadStabilizer.map (MulAut.conj g).toMonoidHom) ∧
      (∃ g : A6, a6SynthemeStabilizer.map β.toMonoidHom =
        a6SynthemeStabilizer.map (MulAut.conj g).toMonoidHom)) := by
  constructor
  · intro h
    exact (natural_iff_preserves_source_parabolic_types β).mp
      ((natural_iff_standard_conjugate β).mpr h.1)
  · intro h
    have hn := (natural_iff_preserves_source_parabolic_types β).mpr h
    exact ⟨(natural_iff_standard_conjugate β).mp hn,
      (natural_iff_second_conjugate β).mp hn⟩

end AlternatingSix.ShadowLocal.FourNormalizers.SixParabolics
