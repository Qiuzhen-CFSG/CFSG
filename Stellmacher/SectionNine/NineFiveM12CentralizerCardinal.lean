import Stellmacher.SectionNine.NineFiveM12NormalizerMaskReduction
open scoped Pointwise
noncomputable section
namespace Stellmacher.SectionNine.M12Realization

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

def pairEncode : (Fin 4 × Fin 2) ⊕ Fin 4 → Fin 12
  | Sum.inl (i,b) =>
    match i, b with
    | 0, 0 => 1 | 0, 1 => 5 | 1, 0 => 3 | 1, 1 => 4
    | 2, 0 => 6 | 2, 1 => 8 | 3, 0 => 10 | 3, 1 => 11
  | Sum.inr i => match i with | 0 => 0 | 1 => 2 | 2 => 7 | 3 => 9

def pairEncodeEquiv : (Fin 4 × Fin 2) ⊕ Fin 4 ≃ Fin 12 where
  toFun := pairEncode
  invFun := ![Sum.inr 0, Sum.inl (0, 0), Sum.inr 1, Sum.inl (1, 0),
    Sum.inl (1, 1), Sum.inl (0, 1), Sum.inl (2, 0), Sum.inr 2,
    Sum.inl (2, 1), Sum.inr 3, Sum.inl (3, 0), Sum.inl (3, 1)]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairCoord (σ : Equiv.Perm (Fin 4)) (flip : Fin 4 → Equiv.Perm (Fin 2)) :
    (Fin 4 × Fin 2) ≃ (Fin 4 × Fin 2) where
  toFun x := (σ x.1, flip x.1 x.2)
  invFun x := (σ.symm x.1, (flip (σ.symm x.1)).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

def centralizerCoord (σ : Equiv.Perm (Fin 4)) (flip : Fin 4 → Equiv.Perm (Fin 2))
    (τ : Equiv.Perm (Fin 4)) : Equiv.Perm ((Fin 4 × Fin 2) ⊕ Fin 4) :=
  Equiv.sumCongr (pairCoord σ flip) τ

def centralizerCandidate (σ : Equiv.Perm (Fin 4)) (flip : Fin 4 → Equiv.Perm (Fin 2))
    (τ : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 12) :=
  (pairEncodeEquiv.symm.trans (centralizerCoord σ flip τ)).trans pairEncodeEquiv

abbrev centralizerParameters :=
  Equiv.Perm (Fin 4) × (Fin 4 → Equiv.Perm (Fin 2)) × Equiv.Perm (Fin 4)

def centralizerCandidate' : centralizerParameters → Equiv.Perm (Fin 12) :=
  fun x => centralizerCandidate x.1 x.2.1 x.2.2

def centralizerCarrier : Finset (Equiv.Perm (Fin 12)) :=
  (Finset.univ : Finset centralizerParameters).image centralizerCandidate'

theorem centralizerCoord_injective : Function.Injective
    (fun x : centralizerParameters => centralizerCoord x.1 x.2.1 x.2.2) := by
  rintro ⟨σ₁, f₁, τ₁⟩ ⟨σ₂, f₂, τ₂⟩ h
  have hp : pairCoord σ₁ f₁ = pairCoord σ₂ f₂ := by
    apply Equiv.ext
    intro x
    have hx := congrArg (fun e => e (Sum.inl x)) h
    exact Sum.inl.inj hx
  have ht : τ₁ = τ₂ := by
    apply Equiv.ext
    intro x
    have hx := congrArg (fun e => e (Sum.inr x)) h
    exact Sum.inr.inj hx
  have hs : σ₁ = σ₂ := by
    apply Equiv.ext
    intro i
    have hx := congrArg Prod.fst (congrArg (fun e => e (i, 0)) hp)
    exact hx
  have hf : f₁ = f₂ := by
    funext i
    have hfi : f₁ i = f₂ i := by
      refine Equiv.ext (fun x => ?_)
      have hx := congrArg Prod.snd (congrArg (fun e => e (i, x)) hp)
      rw [hs] at hx
      change f₁ i x = f₂ i x at hx
      exact hx
    exact hfi
  exact Prod.ext hs (Prod.ext hf ht)

theorem centralizerCandidate_injective : Function.Injective centralizerCandidate' := by
  intro x y h
  have hc : centralizerCoord x.1 x.2.1 x.2.2 =
      centralizerCoord y.1 y.2.1 y.2.2 := by
    apply Equiv.ext
    intro z
    have hz := congrArg
      (fun e : Equiv.Perm (Fin 12) => e (pairEncodeEquiv z)) h
    apply pairEncodeEquiv.injective
    simpa only [centralizerCandidate', centralizerCandidate, Equiv.trans_apply,
      Equiv.symm_apply_apply] using hz
  exact centralizerCoord_injective hc

theorem centralizerCandidate_complete (x : centralizerParameters) :
    centralizerCandidate' x = centralizerCandidate x.1 x.2.1 x.2.2 := rfl

theorem mem_centralizerCarrier (p : Equiv.Perm (Fin 12)) :
    p ∈ centralizerCarrier ↔ ∃ x : centralizerParameters, centralizerCandidate' x = p := by
  simp [centralizerCarrier]

theorem centralizerCarrier_card : centralizerCarrier.card = 9216 := by
  rw [centralizerCarrier, Finset.card_image_of_injective _ centralizerCandidate_injective]
  decide +kernel

namespace CentralizerCompleteness

abbrev Coordinates := (Fin 4 × Fin 2) ⊕ Fin 4

def toggle : Equiv.Perm (Fin 2) := Equiv.swap 0 1

def centerCoord : Equiv.Perm Coordinates :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.refl _) toggle) (Equiv.refl _)

theorem toggle_ne (endpoint : Fin 2) : toggle endpoint ≠ endpoint := by
  revert endpoint
  decide +kernel

theorem centerCoord_fixed_iff (point : Coordinates) :
    centerCoord point = point ↔ ∃ index, point = Sum.inr index := by
  cases point with
  | inl pair =>
    constructor
    · intro fixed
      exact False.elim (toggle_ne pair.2 (congrArg Prod.snd (Sum.inl.inj fixed)))
    · rintro ⟨index, impossible⟩
      cases impossible
  | inr index => simp [centerCoord]

theorem centerPerm_encode (point : Coordinates) :
    centerPerm (pairEncodeEquiv point) = pairEncodeEquiv (centerCoord point) := by
  change centerPerm (pairEncode point) = pairEncode (centerCoord point)
  revert point
  decide +kernel

theorem preserves_fixed (permutation : Equiv.Perm Coordinates)
    (commutes : ∀ point, permutation (centerCoord point) = centerCoord (permutation point))
    (point : Coordinates) :
    centerCoord (permutation point) = permutation point ↔ centerCoord point = point := by
  rw [← commutes point, permutation.injective.eq_iff]

theorem preserves_pairs (permutation : Equiv.Perm Coordinates)
    (commutes : ∀ point, permutation (centerCoord point) = centerCoord (permutation point))
    (pair : Fin 4 × Fin 2) : ∃ image, permutation (Sum.inl pair) = Sum.inl image := by
  cases image_eq : permutation (Sum.inl pair) with
  | inl image => exact ⟨image, rfl⟩
  | inr index =>
    have fixed : centerCoord (permutation (Sum.inl pair)) = permutation (Sum.inl pair) := by
      rw [image_eq]
      rfl
    have := (preserves_fixed permutation commutes _).mp fixed
    obtain ⟨index, impossible⟩ := (centerCoord_fixed_iff _).mp this
    cases impossible

theorem preserves_fixed_points (permutation : Equiv.Perm Coordinates)
    (commutes : ∀ point, permutation (centerCoord point) = centerCoord (permutation point))
    (index : Fin 4) : ∃ image, permutation (Sum.inr index) = Sum.inr image := by
  exact (centerCoord_fixed_iff _).mp
    ((preserves_fixed permutation commutes _).mpr rfl)

theorem coordinates_exist (permutation : Equiv.Perm Coordinates)
    (commutes : ∀ point, permutation (centerCoord point) = centerCoord (permutation point)) :
    ∃ parameters : centralizerParameters,
      centralizerCoord parameters.1 parameters.2.1 parameters.2.2 = permutation := by
  let paired : Fin 4 × Fin 2 → Fin 4 × Fin 2 :=
    fun pair => Classical.choose (preserves_pairs permutation commutes pair)
  have paired_spec (pair : Fin 4 × Fin 2) :
      permutation (Sum.inl pair) = Sum.inl (paired pair) :=
    Classical.choose_spec (preserves_pairs permutation commutes pair)
  let fixed : Fin 4 → Fin 4 :=
    fun index => Classical.choose (preserves_fixed_points permutation commutes index)
  have fixed_spec (index : Fin 4) :
      permutation (Sum.inr index) = Sum.inr (fixed index) :=
    Classical.choose_spec (preserves_fixed_points permutation commutes index)
  have paired_injective : Function.Injective paired := by
    intro first second equal
    apply Sum.inl_injective
    apply permutation.injective
    rw [paired_spec, paired_spec, equal]
  have fixed_injective : Function.Injective fixed := by
    intro first second equal
    apply Sum.inr_injective
    apply permutation.injective
    rw [fixed_spec, fixed_spec, equal]
  have paired_toggle (index : Fin 4) (endpoint : Fin 2) :
      paired (index, toggle endpoint) =
        ((paired (index, endpoint)).1, toggle (paired (index, endpoint)).2) := by
    apply Sum.inl_injective
    have equation := commutes (Sum.inl (index, endpoint))
    change permutation (Sum.inl (index, toggle endpoint)) =
      centerCoord (permutation (Sum.inl (index, endpoint))) at equation
    rw [paired_spec, paired_spec] at equation
    exact equation
  have paired_first (index : Fin 4) (endpoint : Fin 2) :
      (paired (index, endpoint)).1 = (paired (index, 0)).1 := by
    fin_cases endpoint
    · rfl
    · simpa [toggle] using congrArg Prod.fst (paired_toggle index 0)
  let endpoints (index : Fin 4) : Fin 2 → Fin 2 :=
    fun endpoint => (paired (index, endpoint)).2
  have endpoints_injective (index : Fin 4) : Function.Injective (endpoints index) := by
    intro first second equal
    have pair_equal : paired (index, first) = paired (index, second) := by
      apply Prod.ext
      · exact (paired_first index first).trans (paired_first index second).symm
      · exact equal
    exact congrArg Prod.snd (paired_injective pair_equal)
  let flips (index : Fin 4) : Equiv.Perm (Fin 2) :=
    Equiv.ofBijective (endpoints index)
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨endpoints_injective index, rfl⟩)
  let pairs : Fin 4 → Fin 4 := fun index => (paired (index, 0)).1
  have pairs_injective : Function.Injective pairs := by
    intro first second equal
    obtain ⟨endpoint, endpoint_eq⟩ := (flips second).surjective (endpoints first 0)
    have pair_equal : paired (first, 0) = paired (second, endpoint) := by
      apply Prod.ext
      · rw [paired_first second endpoint]
        exact equal
      · exact endpoint_eq.symm
    exact congrArg Prod.fst (paired_injective pair_equal)
  let pairPerm : Equiv.Perm (Fin 4) := Equiv.ofBijective pairs
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨pairs_injective, rfl⟩)
  let fixedPerm : Equiv.Perm (Fin 4) := Equiv.ofBijective fixed
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fixed_injective, rfl⟩)
  refine ⟨⟨pairPerm, flips, fixedPerm⟩, Equiv.ext (fun point => ?_)⟩
  cases point with
  | inl pair =>
    rw [paired_spec]
    change Sum.inl (pairPerm pair.1, flips pair.1 pair.2) = Sum.inl (paired pair)
    apply congrArg Sum.inl
    apply Prod.ext
    · exact (paired_first pair.1 pair.2).symm
    · rfl
  | inr index => exact (fixed_spec index).symm

theorem toggle_commutes (permutation : Equiv.Perm (Fin 2)) (endpoint : Fin 2) :
    permutation (toggle endpoint) = toggle (permutation endpoint) := by
  revert permutation endpoint
  decide +kernel

theorem coordinates_commute (parameters : centralizerParameters) (point : Coordinates) :
    centralizerCoord parameters.1 parameters.2.1 parameters.2.2 (centerCoord point) =
      centerCoord (centralizerCoord parameters.1 parameters.2.1 parameters.2.2 point) := by
  cases point with
  | inl pair =>
    change Sum.inl (parameters.1 pair.1, parameters.2.1 pair.1 (toggle pair.2)) =
      Sum.inl (parameters.1 pair.1, toggle (parameters.2.1 pair.1 pair.2))
    rw [toggle_commutes]
  | inr index => rfl

end CentralizerCompleteness

theorem centralizesCenterPerm_iff_exists_centralizerCandidate (permutation : Equiv.Perm (Fin 12)) :
    CentralizesCenterPerm permutation ↔ ∃ parameters : centralizerParameters,
      centralizerCandidate parameters.1 parameters.2.1 parameters.2.2 = permutation := by
  constructor
  · intro commutes
    let coordinates : Equiv.Perm CentralizerCompleteness.Coordinates :=
      (pairEncodeEquiv.trans permutation).trans pairEncodeEquiv.symm
    have coordinates_spec (point : CentralizerCompleteness.Coordinates) :
        pairEncodeEquiv (coordinates point) = permutation (pairEncodeEquiv point) := by
      simp [coordinates]
    have coordinates_commute (point : CentralizerCompleteness.Coordinates) :
        coordinates (CentralizerCompleteness.centerCoord point) =
          CentralizerCompleteness.centerCoord (coordinates point) := by
      apply pairEncodeEquiv.injective
      rw [coordinates_spec, ← CentralizerCompleteness.centerPerm_encode,
        ← CentralizerCompleteness.centerPerm_encode, coordinates_spec]
      exact congrArg (fun actor : Equiv.Perm (Fin 12) => actor (pairEncodeEquiv point)) commutes
    obtain ⟨parameters, parameters_eq⟩ :=
      CentralizerCompleteness.coordinates_exist coordinates coordinates_commute
    refine ⟨parameters, Equiv.ext (fun point => ?_)⟩
    change pairEncodeEquiv
      (centralizerCoord parameters.1 parameters.2.1 parameters.2.2
        (pairEncodeEquiv.symm point)) = permutation point
    rw [parameters_eq, coordinates_spec, pairEncodeEquiv.apply_symm_apply]
  · rintro ⟨parameters, rfl⟩
    apply Equiv.ext
    intro point
    obtain ⟨coordinate, rfl⟩ := pairEncodeEquiv.surjective point
    change centralizerCandidate parameters.1 parameters.2.1 parameters.2.2
        (centerPerm (pairEncodeEquiv coordinate)) =
      centerPerm (centralizerCandidate parameters.1 parameters.2.1 parameters.2.2
        (pairEncodeEquiv coordinate))
    rw [CentralizerCompleteness.centerPerm_encode]
    simp only [centralizerCandidate, Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [CentralizerCompleteness.centerPerm_encode,
      CentralizerCompleteness.coordinates_commute]



noncomputable def secondLocalCentralizerParameters : Finset centralizerParameters :=
  Finset.univ.filter (fun parameters =>
    M12MaskIndexCheck (centralizerCandidate' parameters))

noncomputable def secondLocalCentralizerCarrier : Finset (Equiv.Perm (Fin 12)) :=
  secondLocalCentralizerParameters.map
    ⟨centralizerCandidate', centralizerCandidate_injective⟩

theorem mem_secondLocalCentralizerCarrier_iff (permutation : Equiv.Perm (Fin 12)) :
    permutation ∈ secondLocalCentralizerCarrier ↔
    PreservesM12Blocks permutation ∧ CentralizesCenterPerm permutation := by
  constructor
  · intro hmem
    obtain ⟨parameters, hparameters, rfl⟩ := Finset.mem_map.mp hmem
    exact ⟨(preservesM12Blocks_iff_maskIndexCheck _ |>.mpr (Finset.mem_filter.mp hparameters).2),
      (centralizesCenterPerm_iff_exists_centralizerCandidate _).mpr ⟨parameters, rfl⟩⟩
  · rintro ⟨hblocks, hcentral⟩
    obtain ⟨parameters, hparameters⟩ :=
      (centralizesCenterPerm_iff_exists_centralizerCandidate permutation).mp hcentral
    apply Finset.mem_map.mpr
    refine ⟨parameters, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hparameters⟩
    exact (preservesM12Blocks_iff_maskIndexCheck _).mp hblocks

theorem secondLocalCentralizerParameters_card :
    secondLocalCentralizerParameters.card = 192 := by
  decide +kernel

theorem secondLocalCentralizerCarrier_card :
    secondLocalCentralizerCarrier.card = 192 := by
  rw [secondLocalCentralizerCarrier, Finset.card_map,
    secondLocalCentralizerParameters_card]

theorem m12_secondLocal_cardinal : Nat.card secondLocal = 192 := by
  rw [secondLocal_card_eq_finset secondLocalCentralizerCarrier
      mem_secondLocalCentralizerCarrier_iff, secondLocalCentralizerCarrier_card]

end Stellmacher.SectionNine.M12Realization
