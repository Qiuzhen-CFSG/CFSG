module
public import ABG.ChapterII.Section1.WreathedBaseFour

/-!
# The two classes of four subgroups in a wreathed group

ABG Chapter II §1 Lemma 2(iv), article p.9 (page-010.tex), states that the
chosen T₀ is a four subgroup, is not conjugate to T, and represents every
other four subgroup. The central involution x and the outer involution z
are distinct and commute, giving T₀ its four-group structure.

The main reduction is that every square-one element commuting with z lies
in T₀. Normal form puts either g or gz in the base; the base involution
classification and the interchange of x₂ and x₃ leave only 1 and x there.
Any four subgroup other than T has an outer involution. Conjugate that
involution to z, apply the reduction to all elements, and compare order four.
Normality of T and z outside the base distinguish the two conjugacy classes.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

public theorem x_commute_z : Commute P.x P.z := by
  have hc : Commute P.z P.u := by
    change P.z * (P.s * P.t) = (P.s * P.t) * P.z
    rw [← mul_assoc, P.z_mul_s, mul_assoc, P.z_mul_t, ← mul_assoc, P.commute]
  exact (hc.pow_right _).symm

public theorem T₀_isFourGroup : IsFourGroup P.T₀ := by
  apply Subgroup.isKleinFour_closure_pair_of_orderOf _ _ P.x_orderOf P.z_orderOf _ P.x_commute_z
  intro he
  apply P.z_not_mem_U
  rw [← he]
  exact P.T_le_U (Subgroup.subset_closure (by simp))

public theorem T₀_not_conjugate_T :
    ¬ ∃ g : S, P.T.map (MulAut.conj g).toMonoidHom = P.T₀ := by
  rintro ⟨g, hg⟩
  have he := Subgroup.normal_iff_map_conj_eq.mp P.T_normal g
  have hTT : P.T = P.T₀ := he.symm.trans hg
  exact P.z_not_mem_U (P.T_le_U
    (hTT ▸ (Subgroup.subset_closure (by simp) : P.z ∈ P.T₀)))

private theorem base_or_mul_z_base (g : S) : g ∈ P.U ∨ g * P.z ∈ P.U := by
  obtain ⟨i, j, b, rfl⟩ := P.exists_normal_form g
  have hb : b.val = 0 ∨ b.val = 1 := by omega
  have hu : P.s ^ i.val * P.t ^ j.val ∈ P.U :=
    P.U.mul_mem (P.U.pow_mem (Subgroup.subset_closure (by simp)) _)
      (P.U.pow_mem (Subgroup.subset_closure (by simp)) _)
  rcases hb with hb | hb
  · left; simpa [hb] using hu
  · right; simpa [hb, mul_assoc, ← pow_two, P.z_sq] using hu

private theorem commute_z_base_cases
    {g : S} (hg : g ∈ P.U) (hg2 : g ^ 2 = 1)
    (hc : Commute g P.z) : g = 1 ∨ g = P.x := by
  have hz2 : P.z * P.x₂ = P.x₃ * P.z := P.z_mul_s_pow _
  have hz3 : P.z * P.x₃ = P.x₂ * P.z := P.z_mul_t_pow _
  rcases P.base_involution_cases hg hg2 with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · subst g
    exact (P.x₂_ne_x₃ (mul_right_cancel (hc.eq.trans hz2))).elim
  · subst g
    exact (P.x₂_ne_x₃ (mul_right_cancel (hc.eq.trans hz3)).symm).elim

public theorem commuting_involution_mem_T₀
    {g : S} (hg2 : g ^ 2 = 1) (hc : Commute g P.z) :
    g ∈ P.T₀ := by
  have hx : P.x ∈ P.T₀ := Subgroup.subset_closure (by simp)
  have hz : P.z ∈ P.T₀ := Subgroup.subset_closure (by simp)
  rcases P.base_or_mul_z_base g with hg | hg
  · rcases P.commute_z_base_cases hg hg2 hc with rfl | rfl
    · exact P.T₀.one_mem
    · exact hx
  · have hgz2 : (g * P.z) ^ 2 = 1 := by rw [hc.mul_pow, hg2, P.z_sq, one_mul]
    have hcz : Commute (g * P.z) P.z := hc.mul_left (Commute.refl _)
    rcases P.commute_z_base_cases hg hgz2 hcz with h | h
    · have he : g = P.z := by
        have hh := congrArg (· * P.z) h
        simpa [mul_assoc, ← pow_two, P.z_sq] using hh
      exact he ▸ hz
    · have he : g = P.x * P.z := by
        have hh := congrArg (· * P.z) h
        simpa [mul_assoc, ← pow_two, P.z_sq] using hh
      exact he ▸ P.T₀.mul_mem hx hz

private theorem four_classification_aux
    (K : Subgroup S) (hK : IsKleinFour K) (hKT : K ≠ P.T) :
    ∃ g : S, P.T₀.map (MulAut.conj g).toMonoidHom = K := by
  have hT := P.T_isFourGroup
  have hT₀ := P.T₀_isFourGroup
  let := hK
  let : IsMulCommutative K := IsKleinFour.isMulCommutative
  let : Finite P.T := Nat.finite_of_card_ne_zero (by rw [hT.card_four]; decide)
  let : Finite P.T₀ := Nat.finite_of_card_ne_zero (by rw [hT₀.card_four]; decide)
  have hnot : ¬K ≤ P.U := by
    intro hKU
    have hle : K ≤ P.T := by
      intro a ha
      have ha2 : a ^ 2 = 1 := by
        simpa [pow_two] using congrArg (fun y : K => (y : S)) (IsKleinFour.mul_self (⟨a, ha⟩ : K))
      rcases P.base_involution_cases (hKU ha) ha2 with h | h | h | h
      · rw [h]; exact P.T.one_mem
      all_goals rw [h]; exact Subgroup.subset_closure (by simp)
    exact hKT (Subgroup.eq_of_le_of_card_ge hle (by rw [hT.card_four, hK.card_four]))
  obtain ⟨a, ha, haU⟩ := Set.not_subset.mp hnot
  have ha2 : a ^ 2 = 1 := by
    simpa [pow_two] using congrArg (fun y : K => (y : S))
      (IsKleinFour.mul_self (⟨a, ha⟩ : K))
  obtain ⟨g, hg⟩ := isConj_iff.mp (P.outer_involution_isConj haU ha2)
  let e := MulAut.conj g
  have he : e a = P.z := hg
  have hmap : K.map e.toMonoidHom = P.T₀ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro y ⟨k, hk, rfl⟩
      apply P.commuting_involution_mem_T₀
      · have hk2 : k ^ 2 = 1 := by
          simpa [pow_two] using congrArg (fun v : K => (v : S)) (IsKleinFour.mul_self (⟨k, hk⟩ : K))
        change (e k) ^ 2 = 1
        simpa only [map_pow, map_one] using congrArg e hk2
      · rw [← he]
        change e k * e a = e a * e k
        rw [← map_mul, ← map_mul]
        exact congrArg e (congrArg (fun v : K => (v : S))
          (IsMulCommutative.is_comm.comm (⟨k, hk⟩ : K) (⟨a, ha⟩ : K)))
    · rw [Subgroup.card_map_of_injective e.injective, hT₀.card_four, hK.card_four]
  refine ⟨g⁻¹, ?_⟩
  rw [← hmap, Subgroup.map_map]
  convert Subgroup.map_id K using 1
  ext k
  simp [e, MulAut.conj_apply, mul_assoc]

/-- ABG II.1 Lemma 2(iv): T₀ represents exactly the four subgroups other than T. -/
public theorem four_subgroup_classes :
    IsFourGroup P.T₀ ∧
      (¬ ∃ g : S, P.T.map (MulAut.conj g).toMonoidHom = P.T₀) ∧
      ∀ K : Subgroup S, IsFourGroup K → K ≠ P.T →
        ∃ g : S, P.T₀.map (MulAut.conj g).toMonoidHom = K :=
  ⟨P.T₀_isFourGroup, P.T₀_not_conjugate_T, P.four_classification_aux⟩

end ABG.Wreathed.Presentation
