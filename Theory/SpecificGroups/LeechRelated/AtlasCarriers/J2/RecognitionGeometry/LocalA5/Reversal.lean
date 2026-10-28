module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.Graph
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.Dihedral

/-!+# The marked edge reversal and its conjugation action

An element fixing both cyclic endpoints sends their generators to nonidentity
powers. In the already embedded A₄, the square-one condition on the reversal
word forces that word to remain unchanged. Thus the fixed reversal centralizes
the full literal edge fixer, without any assumption about its order.
The setwise edge stabilizer is then described using this same reversal.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267; the
conjugation convention for uniqueness systems is left conjugation (p.199).
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry
open Subgroup Theory.GroupTheory.GraphUniquenessSystem EdgeData

private theorem nonidentity_power {u v : Carrier} (hu : orderOf u = 3)
    (hv : v ∈ zpowers u) (hv1 : v ≠ 1) :
    ∃ i : Fin 2, u ^ (i.val + 1) = v := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hu, Finset.mem_image] at hv
  obtain ⟨n, hn, rfl⟩ := hv
  have hn3 : n < 3 := Finset.mem_range.mp hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hv1 (pow_zero u)
  exact ⟨⟨n - 1, by omega⟩, by dsimp; congr 1; omega⟩

private theorem reversal_word_rigid (i j : Fin 2)
    (h : (x ^ (i.val + 1) *
      (x ^ (i.val + 1) * (y ^ (j.val + 1))⁻¹) * (x ^ (i.val + 1))⁻¹) ^ 2 = 1) :
    x ^ (i.val + 1) *
      (x ^ (i.val + 1) * (y ^ (j.val + 1))⁻¹) * (x ^ (i.val + 1))⁻¹ = t := by
  have check : ∀ i j : Fin 2,
      let u := modelX ^ (i.val + 1)
      let v := modelY ^ (j.val + 1)
      let w := u * (u * v⁻¹) * u⁻¹
      w ^ 2 = 1 → w = modelX * (modelX * modelY⁻¹) * modelX⁻¹ := by decide +kernel
  have hm : (modelX ^ (i.val + 1) *
      (modelX ^ (i.val + 1) * (modelY ^ (j.val + 1))⁻¹) *
        (modelX ^ (i.val + 1))⁻¹) ^ 2 = 1 := by
    apply edgeHom_injective
    simpa only [map_pow, map_mul, map_inv, map_one, edgeHom_modelX, edgeHom_modelY] using h
  have he := congrArg edgeHom (check i j hm)
  simpa only [map_pow, map_mul, map_inv, edgeHom_modelX, edgeHom_modelY, t] using he

/-- Every element of the full edge fixer fixes the marked reversal by conjugation. -/
theorem conj_t_of_mem_E {g : Carrier} (hg : g ∈ E) : MulAut.conj g t = t := by
  have hx : MulAut.conj g x ∈ X :=
    (mem_normalizer_iff.mp hg.1 x).mp (mem_zpowers x)
  have hy : MulAut.conj g y ∈ Y :=
    (mem_normalizer_iff.mp hg.2 y).mp (mem_zpowers y)
  have hy1 : y ≠ 1 := by
    exact fun h => x_ne_one ((MulAut.conj conjugator).injective (h.trans (map_one _).symm))
  obtain ⟨i, hi⟩ := nonidentity_power orderOf_x hx
    (fun h => x_ne_one ((MulAut.conj g).injective (h.trans (map_one _).symm)))
  obtain ⟨j, hj⟩ := nonidentity_power
    (((MulAut.conj conjugator).orderOf_eq x).trans orderOf_x) hy
    (fun h => hy1 ((MulAut.conj g).injective (h.trans (map_one _).symm)))
  change y ^ (j.val + 1) = MulAut.conj g y at hj
  have ht : MulAut.conj g t = x ^ (i.val + 1) *
      (x ^ (i.val + 1) * (y ^ (j.val + 1))⁻¹) * (x ^ (i.val + 1))⁻¹ := by
    simp only [t, map_mul, map_inv, ← hi, ← hj]
  have hs : (MulAut.conj g t) ^ 2 = 1 := by rw [← map_pow, t_square, map_one]
  rw [ht] at hs ⊢
  exact reversal_word_rigid i j hs

/-- The fixed reversal centralizes the literal pointwise edge fixer. -/
theorem t_mem_centralizer_E : t ∈ centralizer (E : Set Carrier) := by
  apply mem_centralizer_iff.mpr
  intro g hg
  have h := conj_t_of_mem_E hg
  change g * t * g⁻¹ = t at h
  exact (mul_inv_eq_iff_eq_mul.mp h)

/-- The actual edge-reversal conjugation identity required by equivalence of systems. -/
theorem t_conj_of_mem_E {g : Carrier} (hg : g ∈ E) : t * g * t⁻¹ = g := by
  rw [← mem_centralizer_iff.mp t_mem_centralizer_E g hg, mul_inv_cancel_right]

theorem t_mem_edgeStabilizer : t ∈ edgeStabilizer Carrier base neighbor :=
  Or.inr ⟨t_smul_base, t_smul_neighbor⟩

/-- Every local setwise edge stabilizer either fixes the ends or is the marked
reversal times an element of the local pointwise fixer. -/
theorem mem_K_inf_edgeStabilizer_iff (g : Carrier) :
    g ∈ K ⊓ edgeStabilizer Carrier base neighbor ↔
      g ∈ K ⊓ E ∨ ∃ e ∈ K ⊓ E, g = t * e := by
  constructor
  · rintro ⟨hgK, hf | hs⟩
    · exact Or.inl ⟨hgK, by rw [← edgeFixer_eq]; exact hf⟩
    · refine Or.inr ⟨t⁻¹ * g, ⟨K.mul_mem (K.inv_mem t_mem_K) hgK, ?_⟩, ?_⟩
      · rw [← edgeFixer_eq]
        have hb : t⁻¹ • neighbor = base := by rw [inv_smul_eq_iff, t_smul_base]
        have hn : t⁻¹ • base = neighbor := by rw [inv_smul_eq_iff, t_smul_neighbor]
        exact ⟨by change (t⁻¹ * g) • base = base; rw [mul_smul, hs.1, hb],
          by change (t⁻¹ * g) • neighbor = neighbor; rw [mul_smul, hs.2, hn]⟩
      · simp
  · rintro (hg | ⟨e, he, rfl⟩)
    · exact ⟨hg.1, Or.inl (by rw [← edgeFixer_eq] at hg; exact hg.2)⟩
    · exact ⟨K.mul_mem t_mem_K he.1,
        (edgeStabilizer Carrier base neighbor).mul_mem t_mem_edgeStabilizer
          (Or.inl (by rw [← edgeFixer_eq] at he; exact he.2))⟩

/-- The corresponding identity of literal ambient subgroups. -/
theorem K_inf_edgeStabilizer_eq :
    K ⊓ edgeStabilizer Carrier base neighbor = (K ⊓ E) ⊔ zpowers t := by
  apply le_antisymm
  · intro g hg
    rcases (mem_K_inf_edgeStabilizer_iff g).mp hg with hf | ⟨e, he, rfl⟩
    · exact mem_sup_left hf
    · exact ((K ⊓ E) ⊔ zpowers t).mul_mem
        (mem_sup_right (mem_zpowers t)) (mem_sup_left he)
  · apply sup_le
    · intro g hg
      exact (mem_K_inf_edgeStabilizer_iff g).mpr (Or.inl hg)
    · exact zpowers_le.mpr ⟨t_mem_K, t_mem_edgeStabilizer⟩

end Sporadic.LeechRelated.J2.RecognitionGeometry
