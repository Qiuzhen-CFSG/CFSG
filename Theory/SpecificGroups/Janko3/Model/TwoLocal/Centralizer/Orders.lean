module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S0Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S1Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S2Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S3Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S4Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S5Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C1Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C2Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C3Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C4Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C5Steps

import Mathlib.Tactic.FinCases

/-!
# Orders of the concrete two-local candidates

Finite permutation certificates for the fixed word-generated J₃ two-local
candidates. The retained ATLAS action is on 6156 letters. Packed maps are
checked against words in the preceding generators; all transition identities
are checked by the Lean kernel on every letter. The generating Python script
is discovery and code generation only, and contributes no proof premise.

Source: GLS, volume 3, Table 5.3h, printed p.269; ATLAS J3G1-p6156B0.
-/

namespace Sporadic.Janko3.TwoLocal.CentralizerCertificate
open Theory.GroupTheory OrderCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

public theorem S0H_eq_map : S0H = sylowCandidate.map modelSubgroup.subtype := by
  apply le_antisymm
  · have hgen : ∀ i, S0Gen i ∈ sylowCandidate.map modelSubgroup.subtype := by
      intro i
      fin_cases i
      · change S0G0 ∈ sylowCandidate.map modelSubgroup.subtype
        rw [S0G0_eq_generator]
        exact Subgroup.mem_map.mpr ⟨sylowGenerator 0, sylowGenerator_mem 0, rfl⟩
      · change S0G1 ∈ sylowCandidate.map modelSubgroup.subtype
        rw [S0G1_eq_generator]
        exact Subgroup.mem_map.mpr ⟨sylowGenerator 1, sylowGenerator_mem 1, rfl⟩
      · change S0G2 ∈ sylowCandidate.map modelSubgroup.subtype
        rw [S0G2_eq_generator]
        exact Subgroup.mem_map.mpr ⟨sylowGenerator 2, sylowGenerator_mem 2, rfl⟩
      · change S0G3 ∈ sylowCandidate.map modelSubgroup.subtype
        rw [S0G3_eq_generator]
        exact Subgroup.mem_map.mpr ⟨sylowGenerator 3, sylowGenerator_mem 3, rfl⟩
      · change S0G4 ∈ sylowCandidate.map modelSubgroup.subtype
        rw [S0G4_eq_generator]
        exact Subgroup.mem_map.mpr ⟨sylowGenerator 4, sylowGenerator_mem 4, rfl⟩
      · change (S0G0)⁻¹ ∈ sylowCandidate.map modelSubgroup.subtype
        apply (sylowCandidate.map modelSubgroup.subtype).inv_mem
        rw [S0G0_eq_generator]
        exact Subgroup.mem_map.mpr ⟨sylowGenerator 0, sylowGenerator_mem 0, rfl⟩
      · change (S0G1)⁻¹ ∈ sylowCandidate.map modelSubgroup.subtype
        apply (sylowCandidate.map modelSubgroup.subtype).inv_mem
        rw [S0G1_eq_generator]
        exact Subgroup.mem_map.mpr ⟨sylowGenerator 1, sylowGenerator_mem 1, rfl⟩
      · change (S0G2)⁻¹ ∈ sylowCandidate.map modelSubgroup.subtype
        apply (sylowCandidate.map modelSubgroup.subtype).inv_mem
        rw [S0G2_eq_generator]
        exact Subgroup.mem_map.mpr ⟨sylowGenerator 2, sylowGenerator_mem 2, rfl⟩
      · change (S0G3)⁻¹ ∈ sylowCandidate.map modelSubgroup.subtype
        apply (sylowCandidate.map modelSubgroup.subtype).inv_mem
        rw [S0G3_eq_generator]
        exact Subgroup.mem_map.mpr ⟨sylowGenerator 3, sylowGenerator_mem 3, rfl⟩
      · change (S0G4)⁻¹ ∈ sylowCandidate.map modelSubgroup.subtype
        apply (sylowCandidate.map modelSubgroup.subtype).inv_mem
        rw [S0G4_eq_generator]
        exact Subgroup.mem_map.mpr ⟨sylowGenerator 4, sylowGenerator_mem 4, rfl⟩
    rintro g ⟨w, rfl⟩
    induction w with
    | nil => exact (sylowCandidate.map modelSubgroup.subtype).one_mem
    | cons i w ih => exact (sylowCandidate.map modelSubgroup.subtype).mul_mem (hgen i) ih
  · rw [sylowCandidate, MonoidHom.map_closure]
    apply (Subgroup.closure_le S0H).mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · change (sylowGenerator 0 : Equiv.Perm (Fin 6156)) ∈ S0H
      rw [← S0G0_eq_generator]
      exact ⟨[0], by simp only [evalWord, S0Gen, mul_one]⟩
    · change (sylowGenerator 1 : Equiv.Perm (Fin 6156)) ∈ S0H
      rw [← S0G1_eq_generator]
      exact ⟨[1], by simp only [evalWord, S0Gen, mul_one]⟩
    · change (sylowGenerator 2 : Equiv.Perm (Fin 6156)) ∈ S0H
      rw [← S0G2_eq_generator]
      exact ⟨[2], by simp only [evalWord, S0Gen, mul_one]⟩
    · change (sylowGenerator 3 : Equiv.Perm (Fin 6156)) ∈ S0H
      rw [← S0G3_eq_generator]
      exact ⟨[3], by simp only [evalWord, S0Gen, mul_one]⟩
    · change (sylowGenerator 4 : Equiv.Perm (Fin 6156)) ∈ S0H
      rw [← S0G4_eq_generator]
      exact ⟨[4], by simp only [evalWord, S0Gen, mul_one]⟩

public theorem S0H_order : Nat.card S0H = 128 := by
  rw [S0H_card, S1H_card, S2H_card, S3H_card, S4H_card, S5H_card, S6H,
    wordSubgroup_fin_zero_card]

public theorem C0H_eq_map : C0H = centralizerCandidate.map modelSubgroup.subtype := by
  apply le_antisymm
  · have hgen : ∀ i, C0Gen i ∈ centralizerCandidate.map modelSubgroup.subtype := by
      intro i
      fin_cases i
      · change C0G0 ∈ centralizerCandidate.map modelSubgroup.subtype
        rw [C0G0_eq_generator]
        exact Subgroup.mem_map.mpr ⟨centralizerGenerator 0, centralizerGenerator_mem 0, rfl⟩
      · change C0G1 ∈ centralizerCandidate.map modelSubgroup.subtype
        rw [C0G1_eq_generator]
        exact Subgroup.mem_map.mpr ⟨centralizerGenerator 1, centralizerGenerator_mem 1, rfl⟩
      · change C0G2 ∈ centralizerCandidate.map modelSubgroup.subtype
        rw [C0G2_eq_generator]
        exact Subgroup.mem_map.mpr ⟨centralizerGenerator 2, centralizerGenerator_mem 2, rfl⟩
      · change C0G3 ∈ centralizerCandidate.map modelSubgroup.subtype
        rw [C0G3_eq_generator]
        exact Subgroup.mem_map.mpr ⟨centralizerGenerator 3, centralizerGenerator_mem 3, rfl⟩
      · change C0G4 ∈ centralizerCandidate.map modelSubgroup.subtype
        rw [C0G4_eq_generator]
        exact Subgroup.mem_map.mpr ⟨centralizerGenerator 4, centralizerGenerator_mem 4, rfl⟩
      · change (C0G0)⁻¹ ∈ centralizerCandidate.map modelSubgroup.subtype
        apply (centralizerCandidate.map modelSubgroup.subtype).inv_mem
        rw [C0G0_eq_generator]
        exact Subgroup.mem_map.mpr ⟨centralizerGenerator 0, centralizerGenerator_mem 0, rfl⟩
      · change (C0G1)⁻¹ ∈ centralizerCandidate.map modelSubgroup.subtype
        apply (centralizerCandidate.map modelSubgroup.subtype).inv_mem
        rw [C0G1_eq_generator]
        exact Subgroup.mem_map.mpr ⟨centralizerGenerator 1, centralizerGenerator_mem 1, rfl⟩
      · change (C0G2)⁻¹ ∈ centralizerCandidate.map modelSubgroup.subtype
        apply (centralizerCandidate.map modelSubgroup.subtype).inv_mem
        rw [C0G2_eq_generator]
        exact Subgroup.mem_map.mpr ⟨centralizerGenerator 2, centralizerGenerator_mem 2, rfl⟩
      · change (C0G3)⁻¹ ∈ centralizerCandidate.map modelSubgroup.subtype
        apply (centralizerCandidate.map modelSubgroup.subtype).inv_mem
        rw [C0G3_eq_generator]
        exact Subgroup.mem_map.mpr ⟨centralizerGenerator 3, centralizerGenerator_mem 3, rfl⟩
      · change (C0G4)⁻¹ ∈ centralizerCandidate.map modelSubgroup.subtype
        apply (centralizerCandidate.map modelSubgroup.subtype).inv_mem
        rw [C0G4_eq_generator]
        exact Subgroup.mem_map.mpr ⟨centralizerGenerator 4, centralizerGenerator_mem 4, rfl⟩
    rintro g ⟨w, rfl⟩
    induction w with
    | nil => exact (centralizerCandidate.map modelSubgroup.subtype).one_mem
    | cons i w ih => exact (centralizerCandidate.map modelSubgroup.subtype).mul_mem (hgen i) ih
  · rw [centralizerCandidate, MonoidHom.map_closure]
    apply (Subgroup.closure_le C0H).mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · change (centralizerGenerator 0 : Equiv.Perm (Fin 6156)) ∈ C0H
      rw [← C0G0_eq_generator]
      exact ⟨[0], by simp only [evalWord, C0Gen, mul_one]⟩
    · change (centralizerGenerator 1 : Equiv.Perm (Fin 6156)) ∈ C0H
      rw [← C0G1_eq_generator]
      exact ⟨[1], by simp only [evalWord, C0Gen, mul_one]⟩
    · change (centralizerGenerator 2 : Equiv.Perm (Fin 6156)) ∈ C0H
      rw [← C0G2_eq_generator]
      exact ⟨[2], by simp only [evalWord, C0Gen, mul_one]⟩
    · change (centralizerGenerator 3 : Equiv.Perm (Fin 6156)) ∈ C0H
      rw [← C0G3_eq_generator]
      exact ⟨[3], by simp only [evalWord, C0Gen, mul_one]⟩
    · change (centralizerGenerator 4 : Equiv.Perm (Fin 6156)) ∈ C0H
      rw [← C0G4_eq_generator]
      exact ⟨[4], by simp only [evalWord, C0Gen, mul_one]⟩

public theorem C0H_order : Nat.card C0H = 1920 := by
  rw [C0H_card, C1H_card, C2H_card, C3H_card, C4H_card, C5H_card, C6H,
    wordSubgroup_fin_zero_card]

end Sporadic.Janko3.TwoLocal.CentralizerCertificate

namespace Sporadic.Janko3.TwoLocal
open CentralizerCertificate

/-- The fixed word-defined sylow candidate has order 128. -/
public theorem sylowCandidate_card : Nat.card sylowCandidate = 128 := by
  have h := Subgroup.card_map_of_injective (K := sylowCandidate) modelSubgroup.subtype_injective
  rw [← S0H_eq_map, S0H_order] at h
  exact h.symm

/-- The fixed word-defined centralizer candidate has order 1920. -/
public theorem centralizerCandidate_card : Nat.card centralizerCandidate = 1920 := by
  have h := Subgroup.card_map_of_injective (K := centralizerCandidate) modelSubgroup.subtype_injective
  rw [← C0H_eq_map, C0H_order] at h
  exact h.symm

end Sporadic.Janko3.TwoLocal
