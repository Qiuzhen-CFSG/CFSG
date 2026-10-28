module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry.Centralizers

/-!
# Normal cyclic-four subgroups of the local holomorph

A generator of a normal cyclic-four subgroup must be one of `r²`, `r⁶`,
`r²b`, `r⁶b`: conjugation by `r` already excludes the other elements of
order four. Thus adjoining the marked transposition gives `⟨r²,b⟩` in
every case, and every inner-dihedral involution outside the center inverts
such a subgroup. Normality throughout is in the entire 32-element model.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, pp.569–570.
-/

@[expose] public section
namespace AlternatingSix.ShadowLocal.Holomorph
open Subgroup
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 2000000

private theorem mem_four_words (v x : Model) (hv : orderOf v = 4) :
    x ∈ zpowers v ↔ ∃ i : Fin 4, v ^ i.val = x := by
  rw [mem_zpowers_iff_mem_range_orderOf, hv]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨⟨n, hn⟩, h⟩
  · rintro ⟨i, h⟩
    exact ⟨i.val, i.isLt, h⟩

private def normalFourGenerator (v : Model) : Prop :=
  v = rotation ^ 2 ∨ v = (rotation ^ 2)⁻¹ ∨
    v = rotation ^ 2 * transposition ∨ v = (rotation ^ 2)⁻¹ * transposition

private instance (v : Model) : Decidable (normalFourGenerator v) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

private theorem normalFour_generator (V : Subgroup Model) [IsCyclic V] [V.Normal]
    (hV : Nat.card V = 4) :
    ∃ v : Model, zpowers v = V ∧ orderOf v = 4 ∧ normalFourGenerator v := by
  obtain ⟨v, hv⟩ := V.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hord : orderOf v = 4 := by rw [← Nat.card_zpowers, hv, hV]
  have hpow : v ^ 4 = 1 := by simpa [hord] using pow_orderOf_eq_one v
  have hsq : v ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hd
    norm_num at hd
  have hconj : rotation * v * rotation⁻¹ ∈ zpowers v := by
    rw [hv]
    exact Subgroup.Normal.conj_mem inferInstance v (hv ▸ mem_zpowers v) rotation
  rw [mem_four_words _ _ hord] at hconj
  have table : ∀ v : Model, v ^ 4 = 1 → v ^ 2 ≠ 1 →
      (∃ i : Fin 4, v ^ i.val = rotation * v * rotation⁻¹) →
      normalFourGenerator v := by decide +kernel
  exact ⟨v, hv, hord, table v hpow hsq hconj⟩

/-- Every normal cyclic-four subgroup supplements `P₀` to the same subgroup. -/
theorem normal_cyclicFour_sup_transposition (V : Subgroup Model) [IsCyclic V] [V.Normal]
    (hV : Nat.card V = 4) :
    V ⊔ transpositionSubgroup = cyclicFour ⊔ transpositionSubgroup := by
  obtain ⟨v, hv, _, hgen⟩ := normalFour_generator V hV
  apply le_antisymm
  · apply sup_le _ le_sup_right
    rw [← hv]
    apply zpowers_le.mpr
    rw [mem_cyclicFour_sup_transposition]
    have table : ∀ v : Model, normalFourGenerator v →
        ∃ i, fourTranspositionEmbedding i = v := by decide +kernel
    exact table v hgen
  · apply sup_le _ le_sup_right
    apply zpowers_le.mpr
    have table : ∀ v : Model, normalFourGenerator v →
        ∃ (i : Fin 4) (j : Fin 2), rotation ^ 2 = v ^ i.val * transposition ^ j.val := by
      decide +kernel
    obtain ⟨i, j, hij⟩ := table v hgen
    rw [hij]
    exact Subgroup.mul_mem_sup
      (Subgroup.pow_mem _ (hv ▸ mem_zpowers v) _)
      (Subgroup.pow_mem _ (mem_zpowers _) _)

/-- Noncentral inner-dihedral involutions invert every normal cyclic-four subgroup. -/
theorem inner_involution_inverts_normal_cyclicFour (V : Subgroup Model)
    [IsCyclic V] [V.Normal] (hV : Nat.card V = 4)
    (e : Model) (heD : e ∈ innerD) (heZ : e ∉ centralTwo) (he2 : e ^ 2 = 1) :
    ∀ x ∈ V, e * x * e⁻¹ = x⁻¹ := by
  obtain ⟨v, hv, hord, hgen⟩ := normalFour_generator V hV
  have table : ∀ v e : Model, normalFourGenerator v →
      (∃ d, innerEmbedding d = e) → (¬ ∃ i, centralEmbedding i = e) →
      e ^ 2 = 1 → e * v * e⁻¹ = v⁻¹ := by decide +kernel
  have hinv := table v e hgen ((mem_innerD _).mp heD) ((mem_centralTwo _).not.mp heZ) he2
  intro x hx
  rw [← hv, mem_four_words _ _ hord] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [← conj_pow, hinv, inv_pow]

end AlternatingSix.ShadowLocal.Holomorph
