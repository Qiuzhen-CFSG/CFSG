module

public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Proper Sylow overgroups in characteristic-two SL₂

A matrix with a nonzero lower-left entry, together with all upper
transvections, generates SL₂: an upper row operation makes its upper-left
entry zero, and conjugation then gives every lower transvection. Consequently
a proper overgroup of the upper unipotents is upper triangular and normalizes
them. Sylow conjugacy gives the assertion for every Sylow two-subgroup.

This is the reusable matrix argument from
`CFSG/Quasithin/ChapterF/Section01/RankOneBorels/Linear/MatrixBorel.lean`,
adapted directly to Mathlib's special linear group and upper unipotents.
Source: Aschbacher–Smith, printed pp.259–260, Remark F.1.2 and Lemma F.1.3(1).
-/

@[expose] public section

open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.SolvableParabolic
variable {F : Type*} [Field F]
local notation "SL" => SpecialLinearGroup (Fin 2) F
private abbrev uni (t : F) : SL := SpecialLinearGroup.transvection zero_ne_one t

private theorem lower_of_zero_entry (g : SL) (h00 : g.val 0 0 = 0) (t : F) :
    g * uni t * g⁻¹ =
      SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero
        (-(g.val 1 0 ^ 2 * t)) := by
  have hd := g.property
  simp only [det_fin_two, h00, zero_mul, zero_sub] at hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, adjugate_fin_two, mul_apply, Fin.sum_univ_two,
      SpecialLinearGroup.transvection_coe, h00] <;>
    first | exact hd | simpa only [mul_comm] using hd | ring

private theorem eq_top_of_upper_of_entry (M : Subgroup SL)
    (hU : SpecialLinearGroup.upperUnipotent F ≤ M)
    (g : SL) (hg : g ∈ M) (hc : g.val 1 0 ≠ 0) : M = ⊤ := by
  let a : SL := uni (-(g.val 0 0 / g.val 1 0)) * g
  have ha : a ∈ M := M.mul_mem
    (hU ((SpecialLinearGroup.mem_upperUnipotent F _).mpr ⟨_, rfl⟩)) hg
  have ha00 : a.val 0 0 = 0 := by
    simp [a, uni, SpecialLinearGroup.transvection_coe, mul_apply, Fin.sum_univ_two, hc]
  have ha10 : a.val 1 0 = g.val 1 0 := by
    simp [a, uni, SpecialLinearGroup.transvection_coe, mul_apply, Fin.sum_univ_two]
  have hlower (c : F) :
      SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero c ∈ M := by
    have hmem := M.mul_mem (M.mul_mem ha
      (hU ((SpecialLinearGroup.mem_upperUnipotent F _).mpr
        ⟨-(c / g.val 1 0 ^ 2), rfl⟩))) (M.inv_mem ha)
    rw [lower_of_zero_entry a ha00, ha10] at hmem
    simpa [mul_div_cancel₀ _ (pow_ne_zero 2 hc)] using hmem
  apply top_unique
  intro x _
  refine Matrix.SL2.transvection_induction (fun x => x ∈ M) ?_ ?_ x
  · intro i j hij c
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hU ((SpecialLinearGroup.mem_upperUnipotent F _).mpr ⟨c, rfl⟩)
    · exact hlower c
    · exact (hij rfl).elim
  · exact fun _ _ => M.mul_mem

private theorem upper_conj (g : SL) (hg : g.val 1 0 = 0) (t : F) :
    g * uni t * g⁻¹ = uni (g.val 0 0 ^ 2 * t) := by
  have hd : g.val 0 0 * g.val 1 1 = 1 := by
    simpa only [det_fin_two, hg, mul_zero, sub_zero] using g.property
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, adjugate_fin_two, mul_apply, Fin.sum_univ_two,
      SpecialLinearGroup.transvection_coe, hg] <;>
    first | exact hd | simpa only [mul_comm] using hd | ring

private theorem proper_upper_overgroup (M : Subgroup SL)
    (hU : SpecialLinearGroup.upperUnipotent F ≤ M) (hM : M ≠ ⊤) :
    M ≤ normalizer (SpecialLinearGroup.upperUnipotent F : Set SL) := by
  have hz (g : SL) (hg : g ∈ M) : g.val 1 0 = 0 := by
    by_contra hc
    exact hM (eq_top_of_upper_of_entry M hU g hg hc)
  have hconj (g : SL) (hg : g ∈ M) (u : SL)
      (hu : u ∈ SpecialLinearGroup.upperUnipotent F) :
      g * u * g⁻¹ ∈ SpecialLinearGroup.upperUnipotent F := by
    obtain ⟨t, rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent F u).mp hu
    rw [upper_conj g (hz g hg)]
    exact (SpecialLinearGroup.mem_upperUnipotent F _).mpr ⟨_, rfl⟩
  intro g hg
  apply mem_normalizer_iff.mpr
  intro u
  exact ⟨hconj g hg u, fun hu => by
    simpa [mul_assoc] using hconj g⁻¹ (M.inv_mem hg) _ hu⟩

/-- Every proper overgroup of a Sylow two-subgroup in SL₂ normalizes it. -/
theorem proper_sylow_overgroup [Finite F] [CharP F 2]
    (T : Sylow 2 SL) (H : Subgroup SL) (hH : H ≠ ⊤)
    (hTH : (T : Subgroup SL) ≤ H) : H ≤ normalizer (T : Set SL) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL T
    (SpecialLinearGroup.upperUnipotentSylow F 2)
  let e := MulAut.conj g
  have hT : (T : Subgroup SL).map e.toMonoidHom =
      SpecialLinearGroup.upperUnipotent F := by
    have he := congrArg (fun S : Sylow 2 SL => (S : Subgroup SL)) hg
    exact he
  have hn := proper_upper_overgroup (H.map e.toMonoidHom)
    (hT ▸ Subgroup.map_mono hTH) (by
      intro hh
      apply hH
      apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
      simpa only [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using hh)
  rw [← hT, ← Subgroup.map_equiv_normalizer_eq] at hn
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp hn

end Theory.SpecificGroups.SymplecticFour.SolvableParabolic
