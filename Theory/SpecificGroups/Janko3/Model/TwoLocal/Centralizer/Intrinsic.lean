module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Normal
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.CoreOrder
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Detection
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.FinCases

/-!
# The intrinsic normal two-subgroup of the J₃ local candidate

Finite permutation certificates for the fixed word-generated J₃ two-local
candidates. The retained ATLAS action is on 6156 letters. Packed maps are
checked against words in the preceding generators; all transition identities
are checked by the Lean kernel on every letter. The generating Python script
is discovery and code generation only, and contributes no proof premise.

Source: GLS, volume 3, Table 5.3h, printed p.269; ATLAS J3G1-p6156B0.
-/

namespace Sporadic.Janko3.TwoLocal
open Theory.GroupTheory OrderCertificate CentralizerCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

@[expose] public def centralizerCoreWord : Fin 5 → List (Fin 5)
  | 0 => [0]
  | 1 => [3, 3]
  | 2 => [2, 3, 3, 2]
  | 3 => [4, 2, 4, 2]
  | 4 => [2, 4, 2, 4]

/-- Each generator is intrinsically an element of the fixed local candidate. -/
@[expose] public def centralizerCoreGenerator (i : Fin 5) : centralizerCandidate :=
  evalWord (fun j => ⟨centralizerGenerator j, centralizerGenerator_mem j⟩) (centralizerCoreWord i)

/-- The order-32 normal subgroup constructed by words inside the local group. -/
@[expose] public def centralizerTwoSubgroup : Subgroup centralizerCandidate :=
  Subgroup.closure (Set.range centralizerCoreGenerator)

public theorem centralizerCoreGenerator_mem (i : Fin 5) :
    centralizerCoreGenerator i ∈ centralizerTwoSubgroup := Subgroup.subset_closure ⟨i, rfl⟩

@[expose] public def centralizerEmbedding : centralizerCandidate →* Equiv.Perm (Fin 6156) :=
  modelSubgroup.subtype.comp centralizerCandidate.subtype

public theorem centralizerEmbedding_injective : Function.Injective centralizerEmbedding :=
  modelSubgroup.subtype_injective.comp centralizerCandidate.subtype_injective

private theorem Q0G0_eq_intrinsic : Q0G0 =
    centralizerEmbedding (centralizerCoreGenerator 0) := by
  rw [Q0G0_eq_word]
  simp only [evalWord, C0Gen, C0G0_eq_generator]
  rfl

private theorem Q0G1_eq_intrinsic : Q0G1 =
    centralizerEmbedding (centralizerCoreGenerator 1) := by
  rw [Q0G1_eq_word]
  simp only [evalWord, C0Gen, C0G3_eq_generator]
  rfl

private theorem Q0G2_eq_intrinsic : Q0G2 =
    centralizerEmbedding (centralizerCoreGenerator 2) := by
  rw [Q0G2_eq_word]
  simp only [evalWord, C0Gen, C0G2_eq_generator, C0G3_eq_generator]
  rfl

private theorem Q0G3_eq_intrinsic : Q0G3 =
    centralizerEmbedding (centralizerCoreGenerator 3) := by
  rw [Q0G3_eq_word]
  simp only [evalWord, C0Gen, C0G2_eq_generator, C0G4_eq_generator]
  rfl

private theorem Q0G4_eq_intrinsic : Q0G4 =
    centralizerEmbedding (centralizerCoreGenerator 4) := by
  rw [Q0G4_eq_word]
  simp only [evalWord, C0Gen, C0G2_eq_generator, C0G4_eq_generator]
  rfl

public theorem centralizerTwoSubgroup_map :
    centralizerTwoSubgroup.map centralizerEmbedding = Q0H := by
  symm
  apply le_antisymm
  · have hgen : ∀ i, Q0Gen i ∈ centralizerTwoSubgroup.map centralizerEmbedding := by
      intro i
      fin_cases i
      · change Q0G0 ∈ centralizerTwoSubgroup.map centralizerEmbedding
        rw [Q0G0_eq_intrinsic]
        exact Subgroup.mem_map.mpr ⟨_, centralizerCoreGenerator_mem 0, rfl⟩
      · change Q0G1 ∈ centralizerTwoSubgroup.map centralizerEmbedding
        rw [Q0G1_eq_intrinsic]
        exact Subgroup.mem_map.mpr ⟨_, centralizerCoreGenerator_mem 1, rfl⟩
      · change Q0G2 ∈ centralizerTwoSubgroup.map centralizerEmbedding
        rw [Q0G2_eq_intrinsic]
        exact Subgroup.mem_map.mpr ⟨_, centralizerCoreGenerator_mem 2, rfl⟩
      · change Q0G3 ∈ centralizerTwoSubgroup.map centralizerEmbedding
        rw [Q0G3_eq_intrinsic]
        exact Subgroup.mem_map.mpr ⟨_, centralizerCoreGenerator_mem 3, rfl⟩
      · change Q0G4 ∈ centralizerTwoSubgroup.map centralizerEmbedding
        rw [Q0G4_eq_intrinsic]
        exact Subgroup.mem_map.mpr ⟨_, centralizerCoreGenerator_mem 4, rfl⟩
      · change (Q0G0)⁻¹ ∈ centralizerTwoSubgroup.map centralizerEmbedding
        apply (centralizerTwoSubgroup.map centralizerEmbedding).inv_mem
        rw [Q0G0_eq_intrinsic]
        exact Subgroup.mem_map.mpr ⟨_, centralizerCoreGenerator_mem 0, rfl⟩
      · change (Q0G1)⁻¹ ∈ centralizerTwoSubgroup.map centralizerEmbedding
        apply (centralizerTwoSubgroup.map centralizerEmbedding).inv_mem
        rw [Q0G1_eq_intrinsic]
        exact Subgroup.mem_map.mpr ⟨_, centralizerCoreGenerator_mem 1, rfl⟩
      · change (Q0G2)⁻¹ ∈ centralizerTwoSubgroup.map centralizerEmbedding
        apply (centralizerTwoSubgroup.map centralizerEmbedding).inv_mem
        rw [Q0G2_eq_intrinsic]
        exact Subgroup.mem_map.mpr ⟨_, centralizerCoreGenerator_mem 2, rfl⟩
      · change (Q0G3)⁻¹ ∈ centralizerTwoSubgroup.map centralizerEmbedding
        apply (centralizerTwoSubgroup.map centralizerEmbedding).inv_mem
        rw [Q0G3_eq_intrinsic]
        exact Subgroup.mem_map.mpr ⟨_, centralizerCoreGenerator_mem 3, rfl⟩
      · change (Q0G4)⁻¹ ∈ centralizerTwoSubgroup.map centralizerEmbedding
        apply (centralizerTwoSubgroup.map centralizerEmbedding).inv_mem
        rw [Q0G4_eq_intrinsic]
        exact Subgroup.mem_map.mpr ⟨_, centralizerCoreGenerator_mem 4, rfl⟩
    rintro g ⟨w, rfl⟩
    induction w with
    | nil => exact (centralizerTwoSubgroup.map centralizerEmbedding).one_mem
    | cons i w ih => exact (centralizerTwoSubgroup.map centralizerEmbedding).mul_mem (hgen i) ih
  · rw [centralizerTwoSubgroup, MonoidHom.map_closure]
    apply (Subgroup.closure_le Q0H).mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · change centralizerEmbedding (centralizerCoreGenerator 0) ∈ Q0H
      rw [← Q0G0_eq_intrinsic]
      exact ⟨[0], by simp only [evalWord, Q0Gen, mul_one]⟩
    · change centralizerEmbedding (centralizerCoreGenerator 1) ∈ Q0H
      rw [← Q0G1_eq_intrinsic]
      exact ⟨[1], by simp only [evalWord, Q0Gen, mul_one]⟩
    · change centralizerEmbedding (centralizerCoreGenerator 2) ∈ Q0H
      rw [← Q0G2_eq_intrinsic]
      exact ⟨[2], by simp only [evalWord, Q0Gen, mul_one]⟩
    · change centralizerEmbedding (centralizerCoreGenerator 3) ∈ Q0H
      rw [← Q0G3_eq_intrinsic]
      exact ⟨[3], by simp only [evalWord, Q0Gen, mul_one]⟩
    · change centralizerEmbedding (centralizerCoreGenerator 4) ∈ Q0H
      rw [← Q0G4_eq_intrinsic]
      exact ⟨[4], by simp only [evalWord, Q0Gen, mul_one]⟩

public theorem mem_centralizerTwoSubgroup_iff (x : centralizerCandidate) :
    x ∈ centralizerTwoSubgroup ↔ centralizerEmbedding x ∈ Q0H := by
  rw [← centralizerTwoSubgroup_map]
  exact (Subgroup.mem_map_iff_mem centralizerEmbedding_injective).symm

private theorem centralizerEmbedding_mem (x : centralizerCandidate) :
    centralizerEmbedding x ∈ C0H := by
  rw [C0H_eq_map]
  exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩

/-- Normality is in the local group, not in the ambient J₃ model. -/
public instance centralizerTwoSubgroup_normal : centralizerTwoSubgroup.Normal where
  conj_mem x hx g := by
    apply (mem_centralizerTwoSubgroup_iff _).mpr
    simp only [map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp
      (C0H_le_normalizer_Q0H (centralizerEmbedding_mem g)) _).mp
        ((mem_centralizerTwoSubgroup_iff x).mp hx)

public theorem centralizerTwoSubgroup_card : Nat.card centralizerTwoSubgroup = 32 := by
  have h := Subgroup.card_map_of_injective (K := centralizerTwoSubgroup)
    centralizerEmbedding_injective
  rw [centralizerTwoSubgroup_map, Q0H_order] at h
  exact h.symm

public theorem centralizerTwoSubgroup_isPGroup : IsPGroup 2 centralizerTwoSubgroup :=
  IsPGroup.of_card (n := 5) centralizerTwoSubgroup_card

/-- The explicitly constructed normal two-subgroup is self-centralizing
inside the local candidate. -/
public theorem centralizerTwoSubgroup_selfCentralizing :
    Subgroup.centralizer (centralizerTwoSubgroup : Set centralizerCandidate) ≤
      centralizerTwoSubgroup := by
  intro x hx
  apply (mem_centralizerTwoSubgroup_iff x).mpr
  have hcomm (j : Fin 10) : centralizerEmbedding x * Q0Gen j = Q0Gen j * centralizerEmbedding x := by
    have hj : Q0Gen j ∈ Q0H := ⟨[j], by simp only [evalWord, mul_one]⟩
    rw [← centralizerTwoSubgroup_map] at hj
    obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp hj
    have hh := congrArg centralizerEmbedding ((Subgroup.mem_centralizer_iff.mp hx y hy).symm)
    simpa only [map_mul, he] using hh
  rcases core_centralizer_detection ⟨centralizerEmbedding x, centralizerEmbedding_mem x⟩ hcomm with h | h
  · change centralizerEmbedding x = 1 at h
    rw [h]
    exact Q0H.one_mem
  · change centralizerEmbedding x = Q0G0 at h
    rw [h]
    exact ⟨[0], by simp only [evalWord, Q0Gen, mul_one]⟩

/-- The intrinsic two-core of the fixed order-1920 candidate is self-centralizing. -/
public theorem centralizerCandidate_centralizer_pCore_le :
    Subgroup.centralizer (pCore 2 centralizerCandidate : Set centralizerCandidate) ≤
      pCore 2 centralizerCandidate := by
  have hle : centralizerTwoSubgroup ≤ pCore 2 centralizerCandidate :=
    le_sSup ⟨inferInstance, centralizerTwoSubgroup_isPGroup⟩
  exact (Subgroup.centralizer_le hle).trans (centralizerTwoSubgroup_selfCentralizing.trans hle)

end Sporadic.Janko3.TwoLocal
