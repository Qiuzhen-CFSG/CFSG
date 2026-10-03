module
public import ABG.ChapterII.Section1.WreathedInvolutions
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# The normal four subgroup in the wreathed base

ABG Chapter II §1 Lemma 2(iii), article p.9 (page-010.tex), identifies the
chosen subgroup T with the first omega subgroup of U, mapped into S, and
asserts that it is a normal four subgroup. Unique coordinates distinguish
the two commuting half-powers x₂ and x₃. They generate T, so the elementary
construction from two commuting involutions proves that T is a four group.
The base U centralizes T and z swaps its generators, proving normality.
Finally the classification of square-one base elements identifies the
subtype image of omega₁(U) with T. These results retain the chosen subgroup
needed for the subsequent classification of four subgroups of S.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)
include P in
private theorem half_pos_lt : 0 < 2 ^ (n - 1) ∧ 2 ^ (n - 1) < 2 ^ n := by
  constructor
  · positivity
  · exact Nat.pow_lt_pow_right (by omega) (by have := P.height; omega)

public theorem x₂_ne_one : P.x₂ ≠ 1 := by
  intro h
  have h' : P.s ^ (2 ^ (n - 1) : ℕ) * P.t ^ (0 : ℤ) * P.z ^ (0 : ℤ) =
      P.s ^ (0 : ℤ) * P.t ^ (0 : ℤ) * P.z ^ (0 : ℤ) := by simpa [x₂] using h
  rw [← zpow_natCast] at h'
  have hh := (P.normal_form_zpow_eq_iff _ _ _ _ _ _).mp h'
  have hl : (0 : ℤ) < (2 ^ (n - 1) : ℕ) ∧ (2 ^ (n - 1) : ℕ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast P.half_pos_lt
  rw [Int.emod_eq_of_lt (le_of_lt hl.1) hl.2] at hh
  simp at hh

public theorem x₃_ne_one : P.x₃ ≠ 1 := by
  intro h
  have h' : P.s ^ (0 : ℤ) * P.t ^ (2 ^ (n - 1) : ℕ) * P.z ^ (0 : ℤ) =
      P.s ^ (0 : ℤ) * P.t ^ (0 : ℤ) * P.z ^ (0 : ℤ) := by simpa [x₃] using h
  rw [← zpow_natCast] at h'
  have hh := (P.normal_form_zpow_eq_iff _ _ _ _ _ _).mp h'
  have hl : (0 : ℤ) < (2 ^ (n - 1) : ℕ) ∧ (2 ^ (n - 1) : ℕ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast P.half_pos_lt
  rw [Int.emod_eq_of_lt (le_of_lt hl.1) hl.2] at hh
  simp at hh

public theorem x₂_ne_x₃ : P.x₂ ≠ P.x₃ := by
  intro h
  have h' : P.s ^ (2 ^ (n - 1) : ℕ) * P.t ^ (0 : ℤ) * P.z ^ (0 : ℤ) =
      P.s ^ (0 : ℤ) * P.t ^ (2 ^ (n - 1) : ℕ) * P.z ^ (0 : ℤ) := by simpa [x₂,x₃] using h
  simp only [← zpow_natCast] at h'
  have hh := (P.normal_form_zpow_eq_iff _ _ _ _ _ _).mp h'
  have hl : (0 : ℤ) < (2 ^ (n - 1) : ℕ) ∧ (2 ^ (n - 1) : ℕ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast P.half_pos_lt
  rw [Int.emod_eq_of_lt (le_of_lt hl.1) hl.2] at hh
  simp at hh
public theorem T_eq_closure_pair : P.T = Subgroup.closure ({P.x₂, P.x₃} : Set S) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · rw [P.x_eq_x₂_mul_x₃]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · apply (Subgroup.closure_le _).mpr
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> exact Subgroup.subset_closure (by simp)

public theorem T_le_U : P.T ≤ P.U := by
  rw [P.T_eq_closure_pair]
  apply (Subgroup.closure_le _).mpr
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact P.U.pow_mem (Subgroup.subset_closure (by simp)) _
  · exact P.U.pow_mem (Subgroup.subset_closure (by simp)) _

public theorem T_normal : P.T.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← P.generate]
  apply (Subgroup.closure_le _).mpr
  have hu : P.U ≤ Subgroup.normalizer (P.T : Set S) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro a ha b hb
    have hc := P.commute_of_mem_U ha (P.T_le_U hb)
    simpa [hc.eq] using hb
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact hu (Subgroup.subset_closure (by simp))
  · exact hu (Subgroup.subset_closure (by simp))
  · rw [P.T_eq_closure_pair]
    apply Subgroup.normalizer_le_normalizer_closure
    apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    have hz2 : MulAut.conj P.z P.x₂ = P.x₃ := by
      simp [MulAut.conj_apply, x₂, x₃, P.z_mul_s_pow, mul_assoc]
    have hz3 : MulAut.conj P.z P.x₃ = P.x₂ := by
      simp [MulAut.conj_apply, x₂, x₃, P.z_mul_t_pow, mul_assoc]
    simp [Set.image_insert_eq, hz2, hz3, Set.pair_comm]

public theorem T_isFourGroup : IsFourGroup P.T := by
  rw [P.T_eq_closure_pair]
  exact Subgroup.isKleinFour_closure_pair _ _
    (by simpa [pow_two] using P.x₂_sq) (by simpa [pow_two] using P.x₃_sq)
    P.x₂_ne_one P.x₃_ne_one P.x₂_ne_x₃
    ((show Commute P.s P.t from P.commute).pow_pow _ _)

public theorem T_eq_omega_map :
    P.T = (omega₁ (p := 2) P.U).map P.U.subtype := by
  apply le_antisymm
  · rw [P.T_eq_closure_pair]
    apply (Subgroup.closure_le _).mpr
    intro a ha
    have hin (b : S) (hb : b ∈ P.U) (hb2 : b ^ 2 = 1) :
        b ∈ (omega₁ (p := 2) P.U).map P.U.subtype := by
      refine ⟨⟨b, hb⟩, Subgroup.subset_closure ?_, rfl⟩
      change (⟨b, hb⟩ : P.U) ^ (2 ^ 1) = 1
      apply Subtype.ext
      simpa using hb2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hin P.x₂ (P.U.pow_mem (Subgroup.subset_closure (by simp)) _) P.x₂_sq
    · exact hin P.x₃ (P.U.pow_mem (Subgroup.subset_closure (by simp)) _) P.x₃_sq
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    intro a ha
    have ha2 : (a : S) ^ 2 = 1 := by
      have hh := congrArg (fun v : P.U => (v : S)) ha
      simpa using hh
    change (a : S) ∈ P.T
    rcases P.base_involution_cases a.property ha2 with h | h | h | h
    · rw [h]; exact P.T.one_mem
    all_goals
      rw [h]
      exact Subgroup.subset_closure (by simp)

/-- ABG II.1 Lemma 2(iii), with omega₁(U) viewed as a subgroup of S. -/
public theorem base_four_structure :
    P.T = (omega₁ (p := 2) P.U).map P.U.subtype ∧ IsFourGroup P.T ∧ P.T.Normal :=
  ⟨P.T_eq_omega_map, P.T_isFourGroup, P.T_normal⟩

end ABG.Wreathed.Presentation
