module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.LocalChecks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure

/-!
# Proper full-Sylow overgroups in the actual Higman--Sims carrier

For every double-coset representative, checked words either recover both
ATLAS generators or place it in the involution local or the elementary-eight
normalizer. A proper overgroup cannot contain a generating representative.
Coverage then puts the overgroup in the union of two subgroups, hence in one.
All inclusions use the literal normalizers and the fixed full Sylow.

Source: Aschbacher--Smith A.3.12(18), printed pp.47--48, and the embedding
restriction 1.2.8(1), printed p.506.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.SylowOvergroups
open Subgroup DoubleCoset Theory.GroupTheory Data EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData

private theorem eval_inclusion {n : ℕ} (gs : Fin n → Carrier)
    (fs : Fin n → Fin 100 → Fin 100) (h : ∀ i p, inclusion (gs i) p = fs i p)
    (w : List (Fin n)) (p : Fin 100) : inclusion (evalWord gs w) p = evalFun fs w p := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih => rw [evalWord,map_mul,Equiv.Perm.mul_apply,ih,h,evalFun]

private def gGenerator (j : Fin 270) (i : Fin 8) : Carrier :=
  if h : i.val < 3 then sylowGenerator ⟨i.val,h⟩
  else if i.val = 3 then representative j
  else if h : i.val < 7 then (sylowGenerator ⟨i.val-4,by omega⟩)⁻¹
  else (representative j)⁻¹

private theorem gGenerator_mem (j : Fin 270) (i : Fin 8) (P : Subgroup Carrier)
    (hS : subgroup ≤ P) (hj : representative j ∈ P) : gGenerator j i ∈ P := by
  unfold gGenerator
  split
  · exact hS (subset_closure ⟨_,rfl⟩)
  · split
    · exact hj
    · split
      · exact P.inv_mem (hS (subset_closure ⟨_,rfl⟩))
      · exact P.inv_mem hj

private theorem gGenerator_spec (j : Fin 270) (i : Fin 8) (p : Fin 100) :
    inclusion (gGenerator j i) p = genVal j i p := by
  unfold gGenerator genVal
  split
  · exact (sylow_generator_values _ _).symm
  · split
    · exact representative_value j p
    · split
      · have h := inverse_generator_values ⟨i.val-4,by omega⟩
          ((inclusion (sylowGenerator ⟨i.val-4,by omega⟩)).symm p)
        rw [sylow_generator_values] at h
        change packedMap (siCode ⟨i.val-4,by omega⟩)
          ((inclusion (sylowGenerator ⟨i.val-4,by omega⟩))
            ((inclusion (sylowGenerator ⟨i.val-4,by omega⟩)).symm p)) = _ at h
        rw [Equiv.apply_symm_apply] at h
        exact h.symm
      · exact representative_inverse_value j p

private theorem word_mem {n : ℕ} (gs : Fin n → Carrier) (P : Subgroup Carrier)
    (h : ∀ i, gs i ∈ P) (w : List (Fin n)) : evalWord gs w ∈ P := by
  induction w with
  | nil => exact P.one_mem
  | cons i w ih => exact P.mul_mem (h i) ih

private theorem elementary_zero : elementary 0 = closure {e0} := by
  unfold elementary
  congr 1
  ext x
  constructor
  · rintro ⟨j,hj,rfl⟩
    have hj0 : j = 0 := Fin.ext (by simpa using hj)
    subst j
    rfl
  · rintro rfl
    exact ⟨(0 : Fin 3),by simp,rfl⟩

private theorem subgroup_le_central_local : subgroup ≤ localGroup 0 := by
  apply (closure_le _).mpr
  rintro g ⟨i,rfl⟩
  apply Subgroup.centralizer_le_normalizer
  rw [elementary_zero,Subgroup.centralizer_closure]
  apply mem_centralizer_singleton_iff.mpr
  have h := BlockNormalizer.baseSylow_conjugation i 0
  have hi : (![![1, 3, 4], ![1, 2, 7], ![1, 3, 4]] i (0 : Fin 3) : Fin 8) = 1 := by
    fin_cases i <;> rfl
  rw [hi] at h
  change sylowGenerator i * e0 * (sylowGenerator i)⁻¹ = e0 at h
  exact (mul_inv_eq_iff_eq_mul).mp h

private theorem central_rep_mem (j : Fin 270) (hj : kind j = 0) :
    representative j ∈ localGroup 0 := by
  apply Subgroup.centralizer_le_normalizer
  rw [elementary_zero,Subgroup.centralizer_closure]
  apply mem_centralizer_singleton_iff.mpr
  apply inclusion_injective
  apply Equiv.ext
  intro p
  change inclusion (representative j * e0) p = inclusion (e0 * representative j) p
  simp only [map_mul,Equiv.Perm.mul_apply,representative_value]
  have hh := central_spec j hj p
  rw [small_values,small_values] at hh
  exact hh

private theorem large_rep_mem (j : Fin 270) (hj : kind j = 1) :
    representative j ∈ localGroup 2 := by
  have hgen (k : Fin 3) : representative j * elementaryGenerator k * (representative j)⁻¹ ∈ elementary 2 := by
    let i : Fin 8 := ![(localImage j).1,(localImage j).2.1,(localImage j).2.2] k
    have he : representative j * elementaryGenerator k = small i * representative j := by
      apply inclusion_injective
      apply Equiv.ext
      intro p
      simp only [map_mul,Equiv.Perm.mul_apply,representative_value]
      have hh := local_spec j hj p
      simp only [small_values] at hh
      fin_cases k
      · exact hh.1
      · exact hh.2.1
      · exact hh.2.2
    rw [he,mul_assoc,mul_inv_cancel,mul_one]
    exact small_mem_elementary i 2 i.isLt
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rw [elementary,MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro x ⟨y,⟨k,hk,rfl⟩,rfl⟩
    exact hgen k
  · exact le_of_eq (Nat.card_congr ((MulAut.conj (representative j)).subgroupMap (elementary 2)).toEquiv)

private theorem representative_mem (P : Subgroup Carrier) (hS : subgroup ≤ P) (hP : P ≠ ⊤)
    (j : Fin 270) (hj : representative j ∈ P) : representative j ∈ localGroup 0 ∨ representative j ∈ localGroup 2 := by
  by_cases h0 : kind j = 0
  · exact Or.inl (central_rep_mem j h0)
  by_cases h1 : kind j = 1
  · exact Or.inr (large_rep_mem j h1)
  have h2 : kind j = 2 := by omega
  have hwords := generate_spec j h2
  have he0 : inclusion (evalWord (gGenerator j) (extract0 j)) = generatorA := by
    rw [← OrderCertificate.a_eq_generator]
    apply Equiv.ext
    intro p
    rw [eval_inclusion _ _ (gGenerator_spec j)]
    exact (hwords p).1
  have he1 : inclusion (evalWord (gGenerator j) (extract1 j)) = generatorB := by
    rw [← OrderCertificate.b_eq_generator]
    apply Equiv.ext
    intro p
    rw [eval_inclusion _ _ (gGenerator_spec j)]
    exact (hwords p).2
  have hgen : generated ≤ P.map inclusion := by
    apply (closure_le _).mpr
    rw [Set.insert_subset_iff,Set.singleton_subset_iff]
    exact ⟨⟨_,word_mem _ _ (gGenerator_mem j · P hS hj) _,he0⟩,
      ⟨_,word_mem _ _ (gGenerator_mem j · P hS hj) _,he1⟩⟩
  apply False.elim
  apply hP
  apply top_unique
  intro x _
  obtain ⟨y,hy,he⟩ := hgen x.property
  exact (inclusion_injective he) ▸ hy

/-- Every proper overgroup of the literal full Sylow lies in one of two fixed locals. -/
theorem proper_overgroup_le (P : Subgroup Carrier) (hS : subgroup ≤ P) (hP : P ≠ ⊤) :
    P ≤ localGroup 0 ∨ P ≤ localGroup 2 := by
  apply SubgroupClass.subset_union.mp
  intro x hx
  obtain ⟨j,hj⟩ := double_coset_cover x
  obtain ⟨u,hu,v,hv,he⟩ := mem_doubleCoset.mp hj
  have hm : representative j ∈ P := by
    have hm := P.mul_mem (P.mul_mem (P.inv_mem (hS hu)) hx) (P.inv_mem (hS hv))
    rw [he] at hm
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel,mul_one] using hm
  rcases representative_mem P hS hP j hm with h | h
  · exact Or.inl (he ▸ (localGroup 0).mul_mem ((localGroup 0).mul_mem (subgroup_le_central_local hu) h)
      (subgroup_le_central_local hv))
  · exact Or.inr (he ▸ (localGroup 2).mul_mem ((localGroup 2).mul_mem (BlockNormalizer.baseSylow_le_normalizer hu) h)
      (BlockNormalizer.baseSylow_le_normalizer hv))

end Sporadic.LeechRelated.HS.SylowOvergroups
