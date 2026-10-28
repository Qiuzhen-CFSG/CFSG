module

public import Stellmacher.SectionNine.NineFiveM12NormalizerEnumeration

@[expose] public section

namespace Stellmacher.SectionNine.M12Realization

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem normalizerCoordinatePerm_exists (permutation : Equiv.Perm NormalizerPoint)
    (hclass : ∀ first second : NormalizerPoint,
      (permutation first).1 = (permutation second).1 ↔ first.1 = second.1)
    (horbit : ∀ first second : NormalizerPoint,
      ((permutation first).1, (permutation first).2.1) =
        ((permutation second).1, (permutation second).2.1) ↔
          (first.1, first.2.1) = (second.1, second.2.1)) :
    ∃ parameters, normalizerCoordinatePerm parameters = permutation := by
  classical
  let classMap : Fin 3 → Fin 3 := fun classIndex => (permutation (classIndex, 0, 0)).1
  have hclassMap : Function.Injective classMap := by
    intro first second heq
    exact (hclass (first, 0, 0) (second, 0, 0)).mp heq
  let classPerm := Equiv.ofBijective classMap
    ((Finite.injective_iff_bijective).mp hclassMap)
  let orbitMap : Fin 3 → Fin 2 → Fin 2 := fun classIndex orbitIndex =>
    (permutation (classIndex, orbitIndex, 0)).2.1
  have horbitMap : ∀ classIndex, Function.Injective (orbitMap classIndex) := by
    intro classIndex first second heq
    have hpair := (horbit (classIndex, first, 0) (classIndex, second, 0)).mp
      (Prod.ext ((hclass _ _).mpr rfl) heq)
    exact congrArg Prod.snd hpair
  let orbitPerm := fun classIndex => Equiv.ofBijective (orbitMap classIndex)
    ((Finite.injective_iff_bijective).mp (horbitMap classIndex))
  let endpointMap : Fin 3 × Fin 2 → Fin 2 → Fin 2 := fun point endpoint =>
    (permutation (point.1, point.2, endpoint)).2.2
  have hendpointMap : ∀ point, Function.Injective (endpointMap point) := by
    intro point first second heq
    have hpair := (horbit (point.1, point.2, first) (point.1, point.2, second)).mpr rfl
    have hequal : permutation (point.1, point.2, first) =
        permutation (point.1, point.2, second) :=
      Prod.ext (congrArg (fun entry : Fin 3 × Fin 2 => entry.1) hpair)
        (Prod.ext (congrArg (fun entry : Fin 3 × Fin 2 => entry.2) hpair) heq)
    exact congrArg (fun entry : NormalizerPoint => entry.2.2)
      (permutation.injective hequal)
  let endpointPerm := fun point => Equiv.ofBijective (endpointMap point)
    ((Finite.injective_iff_bijective).mp (hendpointMap point))
  refine ⟨(classPerm, orbitPerm, endpointPerm), ?_⟩
  apply Equiv.ext
  intro point
  apply Prod.ext
  · exact (hclass (point.1, 0, 0) point).mpr rfl
  · apply Prod.ext
    · exact congrArg Prod.snd ((horbit (point.1, point.2.1, 0) point).mpr rfl)
    · rfl

def NormalizerSameStabilizer (first second : Fin 12) : Prop :=
  ∀ element ∈ planePerms, element first = first ↔ element second = second

def NormalizerSameOrbit (first second : Fin 12) : Prop :=
  ∃ element ∈ planePerms, element first = second

instance : DecidableRel NormalizerSameStabilizer := fun _ _ =>
  Finset.decidableDforallFinset

instance : DecidableRel NormalizerSameOrbit := fun _ _ =>
  Finset.decidableExistsAndFinset

theorem normalizer_sameStabilizer_coordinates : ∀ first second : NormalizerPoint,
    NormalizerSameStabilizer (normalizerPointEquiv first) (normalizerPointEquiv second) ↔
      first.1 = second.1 := by decide +kernel

theorem normalizer_sameOrbit_coordinates : ∀ first second : NormalizerPoint,
    NormalizerSameOrbit (normalizerPointEquiv first) (normalizerPointEquiv second) ↔
      (first.1, first.2.1) = (second.1, second.2.1) := by decide +kernel

theorem normalizer_sameStabilizer_map (permutation : Equiv.Perm (Fin 12))
    (hnormal : NormalizesPlanePerms permutation) (first second : Fin 12)
    (hsame : NormalizerSameStabilizer first second) :
    NormalizerSameStabilizer (permutation first) (permutation second) := by
  have hconj := Subgroup.mem_set_normalizer_iff''.mp
    ((normalizesPlanePerms_iff permutation).mp hnormal)
  intro element hmem
  have hsame' := hsame (permutation⁻¹ * element * permutation) ((hconj element).mp hmem)
  change permutation.symm (element (permutation first)) = first ↔
    permutation.symm (element (permutation second)) = second at hsame'
  simpa only [Equiv.symm_apply_eq] using hsame'

theorem normalizer_sameOrbit_map (permutation : Equiv.Perm (Fin 12))
    (hnormal : NormalizesPlanePerms permutation) (first second : Fin 12)
    (hsame : NormalizerSameOrbit first second) :
    NormalizerSameOrbit (permutation first) (permutation second) := by
  have hconj := Subgroup.mem_set_normalizer_iff.mp
    ((normalizesPlanePerms_iff permutation).mp hnormal)
  obtain ⟨element, hmem, heq⟩ := hsame
  refine ⟨permutation * element * permutation⁻¹, (hconj element).mp hmem, ?_⟩
  simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
    congrArg permutation heq

theorem normalizerSymmetricCarrier_complete (permutation : Equiv.Perm (Fin 12))
    (hnormal : NormalizesPlanePerms permutation) : permutation ∈ normalizerSymmetricCarrier := by
  have hinverse : NormalizesPlanePerms permutation⁻¹ :=
    (normalizesPlanePerms_iff _).mpr
      (Subgroup.inv_mem _ ((normalizesPlanePerms_iff _).mp hnormal))
  have hstabilizer : ∀ first second,
      NormalizerSameStabilizer (permutation first) (permutation second) ↔
        NormalizerSameStabilizer first second := by
    intro first second
    constructor
    · intro hsame
      simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
        normalizer_sameStabilizer_map _ hinverse _ _ hsame
    · exact normalizer_sameStabilizer_map _ hnormal _ _
  have horbit : ∀ first second,
      NormalizerSameOrbit (permutation first) (permutation second) ↔
        NormalizerSameOrbit first second := by
    intro first second
    constructor
    · intro hsame
      simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
        normalizer_sameOrbit_map _ hinverse _ _ hsame
    · exact normalizer_sameOrbit_map _ hnormal _ _
  let coordinatePerm := normalizerPointEquiv.symm.permCongr permutation
  have hclassCoordinates : ∀ first second : NormalizerPoint,
      (coordinatePerm first).1 = (coordinatePerm second).1 ↔ first.1 = second.1 := by
    intro first second
    rw [← normalizer_sameStabilizer_coordinates, ← normalizer_sameStabilizer_coordinates]
    simpa only [coordinatePerm, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] using hstabilizer (normalizerPointEquiv first)
        (normalizerPointEquiv second)
  have horbitCoordinates : ∀ first second : NormalizerPoint,
      ((coordinatePerm first).1, (coordinatePerm first).2.1) =
        ((coordinatePerm second).1, (coordinatePerm second).2.1) ↔
          (first.1, first.2.1) = (second.1, second.2.1) := by
    intro first second
    rw [← normalizer_sameOrbit_coordinates, ← normalizer_sameOrbit_coordinates]
    simpa only [coordinatePerm, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] using horbit (normalizerPointEquiv first)
        (normalizerPointEquiv second)
  obtain ⟨parameters, heq⟩ := normalizerCoordinatePerm_exists coordinatePerm
    hclassCoordinates horbitCoordinates
  apply Finset.mem_map.mpr
  refine ⟨parameters, Finset.mem_univ _, ?_⟩
  change normalizerPointEquiv.permCongr (normalizerCoordinatePerm parameters) = permutation
  rw [heq]
  exact normalizerPointEquiv.permCongr.apply_symm_apply permutation

theorem mem_normalizerLocalCarrier_iff (permutation : Equiv.Perm (Fin 12)) :
    permutation ∈ normalizerLocalCarrier ↔
      PreservesM12Blocks permutation ∧ NormalizesPlanePerms permutation := by
  constructor
  · intro hmem
    obtain ⟨parameters, hparameters, rfl⟩ := Finset.mem_map.mp hmem
    exact (Finset.mem_filter.mp hparameters).2
  · intro hmem
    obtain ⟨parameters, _, heq⟩ := Finset.mem_map.mp
      (normalizerSymmetricCarrier_complete permutation hmem.2)
    apply Finset.mem_map.mpr
    refine ⟨parameters, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
    change normalizerParameterPerm parameters = permutation at heq
    simpa only [heq] using hmem

theorem normalizerIntersectionCarrier_eq_filter : normalizerIntersectionCarrier =
    normalizerLocalCarrier.filter CentralizesCenterPerm := by
  ext permutation
  simp only [normalizerIntersectionCarrier, normalizerIntersectionParameters,
    normalizerLocalCarrier, Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨parameters, ⟨hmem, hcentral⟩, rfl⟩
    exact ⟨⟨parameters, hmem, rfl⟩, hcentral⟩
  · rintro ⟨⟨parameters, hmem, rfl⟩, hcentral⟩
    exact ⟨parameters, ⟨hmem, hcentral⟩, rfl⟩

theorem mem_normalizerIntersectionCarrier_iff (permutation : Equiv.Perm (Fin 12)) :
    permutation ∈ normalizerIntersectionCarrier ↔
      PreservesM12Blocks permutation ∧
        NormalizesPlanePerms permutation ∧ CentralizesCenterPerm permutation := by
  rw [normalizerIntersectionCarrier_eq_filter, Finset.mem_filter,
    mem_normalizerLocalCarrier_iff, and_assoc]

theorem firstLocal_card_eq_normalizerLocalParameters :
    Nat.card firstLocal = normalizerLocalParameters.card := by
  rw [firstLocal_card_eq_finset normalizerLocalCarrier mem_normalizerLocalCarrier_iff,
    normalizerLocalCarrier, Finset.card_map]

theorem sylowCandidate_card_eq_normalizerIntersectionParameters :
    Nat.card sylowCandidate = normalizerIntersectionParameters.card := by
  rw [sylowCandidate_card_eq_finset normalizerIntersectionCarrier
    mem_normalizerIntersectionCarrier_iff, normalizerIntersectionCarrier, Finset.card_map]

end Stellmacher.SectionNine.M12Realization
