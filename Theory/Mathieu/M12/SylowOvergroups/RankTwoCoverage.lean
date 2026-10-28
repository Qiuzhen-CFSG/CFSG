module

public import Theory.Mathieu.M12.SylowOvergroups.Coverage
public import Theory.Mathieu.M12.SylowOvergroups.Obstructions
public import Theory.Mathieu.M12.SylowOvergroups.RankTwoGeneration

/-!+# Proper Sylow overgroups in the actual M₁₂ model

The complete Sylow double-coset transversal and the checked generation words
show that every proper overgroup of the marked Sylow subgroup lies in one of
the two concrete parabolics. Each parabolic has order 192. Sylow conjugacy
then gives the same divisibility bound without a fixed marking, excluding a
factor of nine in any proper Sylow overgroup.

Source: GLS3 Table 5.3b; Aschbacher--Smith, 15.3.41--42, printed p.1138.
This proves exhaustive containment, without assuming a maximal-subgroup
catalogue or an extension splitting.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups

private theorem eq_top_of_standardGenerators (H : Subgroup M12)
    (hS : sylowCandidate ≤ H) (hgen : ∀ j : Fin 2, standardGenerator j ∈ H) :
    H = ⊤ := by
  have hw (w : List (Fin 2)) : standardWord w ∈ H := by
    induction w with
    | nil => exact H.one_mem
    | cons j w ih => exact H.mul_mem (hgen j) ih
  apply top_unique
  intro g _
  obtain ⟨i, s, t, rfl⟩ := covers g
  exact H.mul_mem (H.mul_mem (hS s.property) (hw _)) (hS t.property)

/-- Every proper overgroup of the marked Sylow subgroup is contained in one
of the two literal parabolics, with no arithmetic exclusion premises. -/
theorem parabolic_containment_of_ne_top (H : Subgroup M12)
    (hS : sylowCandidate ≤ H) (hproper : H ≠ ⊤) :
    H ≤ firstParabolic ∨ H ≤ secondParabolic := by
  apply SubgroupClass.subset_union.mp
  intro g hg
  obtain ⟨i, s, t, rfl⟩ := covers g
  have hi : representative i ∈ H := by
    have h := H.mul_mem (H.mul_mem (H.inv_mem (hS s.property)) hg)
      (H.inv_mem (hS t.property))
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  have hcases : representative i ∈ firstParabolic ∨ representative i ∈ secondParabolic := by
    by_cases h0 : i = 0
    · exact Or.inl (h0 ▸ representative_zero ▸ firstParabolic.one_mem)
    by_cases h37 : i = 37
    · exact Or.inl (h37 ▸ representative_37_mem_first)
    by_cases h41 : i = 41
    · exact Or.inr (h41 ▸ representative_41_mem_second)
    exact (hproper (eq_top_of_standardGenerators H hS
      (standardGenerators_mem_of_representative H hS i hi h0 h37 h41))).elim
  rcases hcases with h | h
  · exact Or.inl (firstParabolic.mul_mem
      (firstParabolic.mul_mem s.property.1 h) t.property.1)
  · exact Or.inr (secondParabolic.mul_mem
      (secondParabolic.mul_mem s.property.2 h) t.property.2)

/-- The order of any proper Sylow overgroup divides 192. -/
theorem card_dvd_192_of_ne_top (H : Subgroup M12) (hproper : H ≠ ⊤)
    (hP : ∃ P : Sylow 2 M12, (P : Subgroup M12) ≤ H) : Nat.card H ∣ 192 := by
  obtain ⟨P, hP⟩ := hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 P commonSylow
  let e := MulAut.conj g
  have hS : sylowCandidate ≤ H.map e.toMonoidHom := by
    have he := congrArg (fun T : Sylow 2 M12 => (T : Subgroup M12)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at he
    change (P : Subgroup M12).map e.toMonoidHom = sylowCandidate at he
    rw [← he]
    exact map_mono hP
  have hn : H.map e.toMonoidHom ≠ ⊤ := by
    intro h
    apply hproper
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [h, map_top_of_surjective _ e.surjective]
  have hd : Nat.card (H.map e.toMonoidHom) ∣ 192 := by
    rcases parabolic_containment_of_ne_top _ hS hn with h | h
    · simpa only [card_firstParabolic] using card_dvd_of_le h
    · simpa only [card_secondParabolic] using card_dvd_of_le h
  rwa [card_map_of_injective e.injective] at hd

/-- A factor of nine forces a Sylow overgroup to be the whole M₁₂. -/
theorem eq_top_of_nine_dvd (H : Subgroup M12) (h9 : 9 ∣ Nat.card H)
    (hP : ∃ P : Sylow 2 M12, (P : Subgroup M12) ≤ H) : H = ⊤ := by
  by_contra hproper
  have h := h9.trans (card_dvd_192_of_ne_top H hproper hP)
  norm_num at h

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
