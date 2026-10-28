module

public import Theory.Mathieu.M12.SmallParabolicPair.Centralizers

/-! Finite permutation predicates for the marked parabolic subgroups, adapted
from `Stellmacher.SectionNine.NineFiveM12LocalMembership`. The normalizer is
`secondParabolic` here; subgroup normality and membership are relative to M₁₂. -/

@[expose] public section

open scoped Pointwise

noncomputable section

namespace Sporadic.Mathieu.M12SmallPair.SylowEnumeration

open Sporadic.Mathieu

def planePerms : Finset (Equiv.Perm (Fin 12)) :=
  {1, zPerm, vPerm, zPerm * vPerm}

def PreservesM12Blocks (permutation : Equiv.Perm (Fin 12)) : Prop :=
  permutation • m12Blocks = m12Blocks

def NormalizesPlanePerms (permutation : Equiv.Perm (Fin 12)) : Prop :=
  planePerms.image (fun element => permutation * element * permutation⁻¹) = planePerms

def CentralizesCenterPerm (permutation : Equiv.Perm (Fin 12)) : Prop :=
  permutation * zPerm = zPerm * permutation

instance : DecidablePred PreservesM12Blocks := fun _ => inferInstanceAs (Decidable (_ = _))

instance : DecidablePred NormalizesPlanePerms := fun _ => inferInstanceAs (Decidable (_ = _))

instance : DecidablePred CentralizesCenterPerm := fun _ => inferInstanceAs (Decidable (_ = _))

theorem mem_M12_iff_preservesBlocks (permutation : Equiv.Perm (Fin 12)) :
    permutation ∈ M12 ↔ PreservesM12Blocks permutation := by
  rw [mem_M12_iff]
  unfold PreservesM12Blocks
  rw [← Finset.coe_inj]
  simp only [Finset.coe_smul_finset]

theorem mem_planePerms_iff (permutation : Equiv.Perm (Fin 12)) :
    permutation ∈ planePerms ↔ permutation = 1 ∨ permutation = zPerm ∨
      permutation = vPerm ∨ permutation = zPerm * vPerm := by
  simp [planePerms]

theorem mem_natural_iff_coe (element : M12) :
    element ∈ natural ↔ (element : Equiv.Perm (Fin 12)) ∈ planePerms := by
  rw [mem_natural, mem_planePerms_iff]
  exact or_congr Subtype.ext_iff
    (or_congr Subtype.ext_iff (or_congr Subtype.ext_iff Subtype.ext_iff))

theorem natural_map_carrier :
    ((natural.map M12.subtype : Subgroup (Equiv.Perm (Fin 12))) : Set _) =
      (planePerms : Set (Equiv.Perm (Fin 12))) := by
  ext permutation
  simp only [Subgroup.mem_map, SetLike.mem_coe]
  constructor
  · rintro ⟨element, hmem, rfl⟩
    exact (mem_natural_iff_coe element).mp hmem
  · intro hmem
    have hgroup : permutation ∈ M12 := by
      rcases (mem_planePerms_iff permutation).mp hmem with rfl | rfl | rfl | rfl
      · exact M12.one_mem
      · exact zPerm_mem
      · exact vPerm_mem
      · exact M12.mul_mem zPerm_mem vPerm_mem
    exact ⟨⟨permutation, hgroup⟩, (mem_natural_iff_coe _).mpr hmem, rfl⟩

theorem normalizesPlanePerms_iff (permutation : Equiv.Perm (Fin 12)) :
    NormalizesPlanePerms permutation ↔
      permutation ∈ Subgroup.normalizer (planePerms : Set _) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  unfold NormalizesPlanePerms
  rw [← Finset.coe_inj]
  simp only [Finset.coe_image, MulAut.conj_apply]
  rfl

theorem mem_secondParabolic_iff (element : M12) :
    element ∈ secondParabolic ↔ NormalizesPlanePerms (element : Equiv.Perm (Fin 12)) := by
  rw [normalizesPlanePerms_iff, ← natural_map_carrier]
  have hnormalizer := Subgroup.comap_normalizer_eq_of_le_range
    (f := M12.subtype) (H := natural.map M12.subtype)
    (Subgroup.map_le_range M12.subtype natural)
  rw [Subgroup.comap_map_eq_self_of_injective M12.subtype_injective] at hnormalizer
  change element ∈ Subgroup.normalizer (natural : Set M12) ↔
    element ∈ (Subgroup.normalizer (natural.map M12.subtype)).comap M12.subtype
  rw [hnormalizer]

theorem mem_firstParabolic_iff (element : M12) :
    element ∈ firstParabolic ↔ CentralizesCenterPerm (element : Equiv.Perm (Fin 12)) := by
  rw [firstParabolic, Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext_iff

theorem mem_sylowCandidate_iff (element : M12) :
    element ∈ sylowCandidate ↔ NormalizesPlanePerms (element : Equiv.Perm (Fin 12)) ∧
      CentralizesCenterPerm (element : Equiv.Perm (Fin 12)) := by
  exact (and_congr (mem_firstParabolic_iff element) (mem_secondParabolic_iff element)).trans and_comm

def localPermEquiv (subgroup : Subgroup M12) (predicate : Equiv.Perm (Fin 12) → Prop)
    (hpredicate : ∀ element : M12, element ∈ subgroup ↔ predicate element) :
    subgroup ≃ {permutation : Equiv.Perm (Fin 12) //
      PreservesM12Blocks permutation ∧ predicate permutation} where
  toFun element := ⟨element.val.val,
    (mem_M12_iff_preservesBlocks _).mp element.val.property,
    (hpredicate element.val).mp element.property⟩
  invFun permutation := ⟨⟨permutation.val,
    (mem_M12_iff_preservesBlocks _).mpr permutation.property.1⟩,
    (hpredicate _).mpr permutation.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem local_card_eq_finset (subgroup : Subgroup M12)
    (predicate : Equiv.Perm (Fin 12) → Prop)
    (hpredicate : ∀ element : M12, element ∈ subgroup ↔ predicate element)
    (carrier : Finset (Equiv.Perm (Fin 12)))
    (hcarrier : ∀ permutation, permutation ∈ carrier ↔
      PreservesM12Blocks permutation ∧ predicate permutation) :
    Nat.card subgroup = carrier.card :=
  (Nat.card_congr (localPermEquiv subgroup predicate hpredicate)).trans
    (Nat.subtype_card carrier hcarrier)

theorem secondParabolic_card_eq_finset (carrier : Finset (Equiv.Perm (Fin 12)))
    (hcarrier : ∀ permutation, permutation ∈ carrier ↔
      PreservesM12Blocks permutation ∧ NormalizesPlanePerms permutation) :
    Nat.card secondParabolic = carrier.card :=
  local_card_eq_finset secondParabolic NormalizesPlanePerms mem_secondParabolic_iff carrier hcarrier

theorem firstParabolic_card_eq_finset (carrier : Finset (Equiv.Perm (Fin 12)))
    (hcarrier : ∀ permutation, permutation ∈ carrier ↔
      PreservesM12Blocks permutation ∧ CentralizesCenterPerm permutation) :
    Nat.card firstParabolic = carrier.card :=
  local_card_eq_finset firstParabolic CentralizesCenterPerm mem_firstParabolic_iff carrier hcarrier

theorem sylowCandidate_card_eq_finset (carrier : Finset (Equiv.Perm (Fin 12)))
    (hcarrier : ∀ permutation, permutation ∈ carrier ↔
      PreservesM12Blocks permutation ∧
        NormalizesPlanePerms permutation ∧ CentralizesCenterPerm permutation) :
    Nat.card sylowCandidate = carrier.card :=
  local_card_eq_finset sylowCandidate
    (fun permutation => NormalizesPlanePerms permutation ∧ CentralizesCenterPerm permutation)
    mem_sylowCandidate_iff carrier hcarrier

end Sporadic.Mathieu.M12SmallPair.SylowEnumeration
