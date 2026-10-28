module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.Representatives
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.KernelNormalizer
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.RepresentativeGeneration.Certificates

/-!
# Generation for the five-overgroup representatives of the Tits group

Explicit, kernel-checked words recover the two standard Atlas generators from
max4 and each nonzero max4 representative. They also recover those generators
from each pair of five-kernels except row 5. In that exceptional row they recover
the two generators of an explicit conjugate of the literal max4 subgroup.
Word membership therefore proves exactly the two generation families consumed
by `MinimumIndexFiveOvergroups.coverage_of_certificates`.

The representatives and candidate subgroups are the shared definitions, and
conjugation is `g*x*g⁻¹`. This module uses neither double-coset coverage nor a
maximal-subgroup catalogue. Source: primary ATLAS Tits max4 and max8 programs,
preserved in `MinimumIndex/source/`; discovery witnesses are in
`RepresentativeGeneration/source/`.
-/

namespace Tits.MinimumIndexFiveOvergroups
open Subgroup FiveFrobenius MinimumIndexCandidates RepresentativeGeneration

private theorem eval_mem {n : Nat} (H : Subgroup Atlas1600Group)
    (a : Fin n → Atlas1600Group) (ha : ∀ k, a k ∈ H)
    (w : List (Fin n × Bool)) : eval a w ∈ H := by
  apply H.list_prod_mem
  intro g hg
  obtain ⟨⟨k, b⟩, _, rfl⟩ := List.mem_map.mp hg
  split
  · exact ha k
  · exact H.inv_mem (ha k)

private theorem eq_top_of_standard_mem (H : Subgroup Atlas1600Group)
    (ha : standard 0 ∈ H) (hb : standard 1 ∈ H) : H = ⊤ := by
  let f : Atlas1600Group →* Equiv.Perm (Fin 1600) := atlas1600Subgroup.subtype
  have h : atlas1600Subgroup ≤ H.map f := by
    apply (closure_le _).mpr
    rintro x (rfl | rfl)
    · exact ⟨standard 0, ha, rfl⟩
    · exact ⟨standard 1, hb, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := h x.property
  exact (show y = x from Subtype.ext he) ▸ hy

private theorem pair_mem (i : Fin 25) (k : Fin 4) :
    pair i k ∈ kernel ⊔ kernel.map (MulAut.conj (max8Rep i)).toMonoidHom := by
  have hv : v ∈ kernel := by rw [kernel_eq_closure]; exact subset_closure (by simp)
  have hu : u ∈ kernel := by rw [kernel_eq_closure]; exact subset_closure (by simp)
  fin_cases k
  · exact mem_sup_left hv
  · exact mem_sup_left hu
  · exact mem_sup_right (mem_map_of_mem (MulAut.conj (max8Rep i)).toMonoidHom hv)
  · exact mem_sup_right (mem_map_of_mem (MulAut.conj (max8Rep i)).toMonoidHom hu)

private theorem max4_map_le (g : Atlas1600Group) (H : Subgroup Atlas1600Group)
    (h : ∀ j : Fin 2, g * (![max4Generators.1, max4Generators.2] j) * g⁻¹ ∈ H) :
    max4.map (MulAut.conj g).toMonoidHom ≤ H := by
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  rintro x (rfl | rfl)
  · change g * max4Generators.1 * g⁻¹ ∈ H
    simpa only [Matrix.cons_val_zero] using h 0
  · change g * max4Generators.2 * g⁻¹ ∈ H
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using h 1

/-- Each nonidentity max8 representative gives a pair of five-kernels containing
an actual conjugate of the literal ATLAS max4 subgroup. -/
public theorem max8_pair_generates (i : Fin 25) (hi : i ≠ 0) :
    ∃ g : Atlas1600Group,
      max4.map (MulAut.conj g).toMonoidHom ≤
        kernel ⊔ kernel.map (MulAut.conj (max8Rep i)).toMonoidHom := by
  let k : Fin 24 := ⟨i.val - 1, by omega⟩
  have hik : (⟨k.val + 1, by omega⟩ : Fin 25) = i := by
    apply Fin.ext
    dsimp [k]
    have hpos : 0 < i.val := by
      by_contra h
      exact hi (Fin.ext (by change i.val = 0; omega))
    omega
  let H := kernel ⊔ kernel.map (MulAut.conj (max8Rep i)).toMonoidHom
  have hm (j : Fin 2) : target8 k j ∈ H := by
    rw [← recovery8_eq k j, hik]
    exact eval_mem H (pair i) (pair_mem i) _
  by_cases hk : k = 4
  · refine ⟨exceptionalConjugator, max4_map_le exceptionalConjugator H ?_⟩
    intro j
    simpa only [target8, hk, ↓reduceIte] using hm j
  · have htop : H = ⊤ := eq_top_of_standard_mem H
        (by simpa only [target8, hk, ↓reduceIte] using hm 0)
        (by simpa only [target8, hk, ↓reduceIte] using hm 1)
    refine ⟨1, ?_⟩
    change _ ≤ H
    rw [htop]
    exact le_top

private theorem extension_mem (i : Fin 7) (k : Fin 3) :
    extension i k ∈ max4 ⊔ closure {max4Rep i} := by
  fin_cases k <;> simp only [extension, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact mem_sup_left (subset_closure (by simp))
  · exact mem_sup_left (subset_closure (by simp))
  · exact mem_sup_right (subset_closure (Set.mem_singleton _))

/-- Each nonidentity max4 representative, together with the literal max4
subgroup, generates the entire Atlas1600Group. -/
public theorem max4_rep_generates (i : Fin 7) (hi : i ≠ 0) :
    max4 ⊔ closure {max4Rep i} = ⊤ := by
  let k : Fin 6 := ⟨i.val - 1, by omega⟩
  have hik : (⟨k.val + 1, by omega⟩ : Fin 7) = i := by
    apply Fin.ext
    dsimp [k]
    have hpos : 0 < i.val := by
      by_contra h
      exact hi (Fin.ext (by change i.val = 0; omega))
    omega
  have hm (j : Fin 2) : standard j ∈ max4 ⊔ closure {max4Rep i} := by
    rw [← recovery4_eq k j, hik]
    exact eval_mem _ (extension i) (extension_mem i) _
  exact eq_top_of_standard_mem _ (hm 0) (hm 1)

end Tits.MinimumIndexFiveOvergroups
