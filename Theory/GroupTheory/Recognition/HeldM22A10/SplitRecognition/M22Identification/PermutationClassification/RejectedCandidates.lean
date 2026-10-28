module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Candidates
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.FinCases

/-!
# Excluding Janko's first and third terminal candidates

An explicit elementary group of order nine in `firstModel` is normalized by
144 distinct words in its generators. Every word identity, multiplication,
conjugation, and distinctness calculation is checked by Lean's kernel. Thus
an embedding into a group of order 443520 with Sylow-three normalizers of
order 72 is impossible. A checked relabeling transfers this obstruction to
`thirdModel`, without appealing to an identification with the Mathieu group M11.

This supplies the exclusion step in Section 9, p.18 of Z. Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
1–19, DOI 10.1016/0021-8693(68)90002-1. GAP was used only to discover words;
its computations are not part of the proof.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification
open Subgroup JankoModel
set_option maxRecDepth 100000

private def a : Equiv.Perm (Fin 22) :=
  List.formPerm [3,8,5] * List.formPerm [4,7,11] * List.formPerm [6,10,9] *
  List.formPerm [14,19,16] * List.formPerm [15,18,22] * List.formPerm [17,21,20]
private def b : Equiv.Perm (Fin 22) :=
  List.formPerm [3,11,20] * List.formPerm [4,17,8] * List.formPerm [5,7,21] *
  List.formPerm [6,19,15] * List.formPerm [9,14,22] * List.formPerm [10,16,18]
private def c : Equiv.Perm (Fin 22) :=
  List.formPerm [1,2,12,13] * List.formPerm [3,15,5,10,20,18,17,19] *
  List.formPerm [4,16,21,9,7,6,8,14] * Equiv.swap 11 22
private def d : Equiv.Perm (Fin 22) :=
  Equiv.swap 2 13 * List.formPerm [3,15,20,18] * List.formPerm [4,9,7,14] *
  List.formPerm [5,19,17,10] * List.formPerm [6,21,16,8] * Equiv.swap 11 22

private def pelt (i : Fin 3 × Fin 3) : Equiv.Perm (Fin 22) := a ^ i.1.val * b ^ i.2.val
private theorem pelt_one : pelt (0,0) = 1 := by decide +kernel
private theorem pelt_mul : ∀ i j : Fin 3 × Fin 3,
    pelt i * pelt j = pelt (i.1 + j.1, i.2 + j.2) := by decide +kernel
private theorem pelt_inv : ∀ i : Fin 3 × Fin 3,
    (pelt i)⁻¹ = pelt (-i.1, -i.2) := by decide +kernel
private theorem pelt_inj_point : Function.Injective (fun i => pelt i 3) := by decide +kernel
private theorem pelt_inj : Function.Injective pelt := by
  intro i j h
  exact pelt_inj_point (congrArg (fun g : Equiv.Perm (Fin 22) => g 3) h)

private def nine : Subgroup (Equiv.Perm (Fin 22)) where
  carrier := Set.range pelt
  one_mem' := ⟨(0,0), pelt_one⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨(i.1 + j.1, i.2 + j.2), (pelt_mul i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨(-i.1, -i.2), (pelt_inv i).symm⟩

private theorem nine_card : Nat.card nine = 9 := by
  exact (Nat.card_congr (Equiv.ofInjective pelt pelt_inj).symm).trans (by simp)

private theorem c_normalizes : ∀ i : Fin 3 × Fin 3,
    ∃ j : Fin 3 × Fin 3, c * pelt i * c⁻¹ = pelt j := by decide +kernel
private theorem d_normalizes : ∀ i : Fin 3 × Fin 3,
    ∃ j : Fin 3 × Fin 3, d * pelt i * d⁻¹ = pelt j := by decide +kernel

private theorem normalizes_of_pelt (g : Equiv.Perm (Fin 22))
    (h : ∀ i : Fin 3 × Fin 3, ∃ j : Fin 3 × Fin 3, g * pelt i * g⁻¹ = pelt j) :
    g ∈ normalizer (nine : Set (Equiv.Perm (Fin 22))) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := h i
    exact ⟨j, hj.symm⟩
  · rw [card_map_of_injective (MulAut.conj g).injective]

private def nelt (i : (Fin 3 × Fin 3) × (Fin 8 × Fin 2)) : Equiv.Perm (Fin 22) :=
  pelt i.1 * c ^ i.2.1.val * d ^ i.2.2.val

private theorem nelt_inj_points :
    Function.Injective (fun i => (nelt i 1, nelt i 3, nelt i 4)) := by decide +kernel

private def gen : Fin 6 → Equiv.Perm (Fin 22)
  | 0 => ell
  | 1 => m
  | 2 => n1
  | 3 => ell⁻¹
  | 4 => m⁻¹
  | 5 => n1⁻¹

private theorem gen_mem (i : Fin 6) : gen i ∈ firstModel := by
  have hl : ell ∈ firstModel := subset_closure (by simp)
  have hm : m ∈ firstModel := subset_closure (by simp)
  have hn : n1 ∈ firstModel := subset_closure (by simp)
  fin_cases i
  · exact hl
  · exact hm
  · exact hn
  · exact firstModel.inv_mem hl
  · exact firstModel.inv_mem hm
  · exact firstModel.inv_mem hn

private theorem word_mem (w : List (Fin 6)) : evalWord gen w ∈ firstModel := by
  induction w with
  | nil => exact firstModel.one_mem
  | cons i w ih => exact firstModel.mul_mem (gen_mem i) ih

private theorem a_word : a = evalWord gen [2,2,4,0,4] := by decide +kernel
private theorem b_word : b = evalWord gen [0,1,0,4,2,3,3,5,5] := by decide +kernel
private theorem c_word : c = evalWord gen [0,1,5,3,5,3,3,1,5,0,0] := by decide +kernel
private theorem d_word : d = evalWord gen [3,2,2,3,1,5,3,5,5,5] := by decide +kernel

private theorem pelt_mem (i : Fin 3 × Fin 3) : pelt i ∈ firstModel := by
  exact firstModel.mul_mem (firstModel.pow_mem (a_word ▸ word_mem _) _)
    (firstModel.pow_mem (b_word ▸ word_mem _) _)

private theorem nine_le : nine ≤ firstModel := by
  rintro _ ⟨i, rfl⟩
  exact pelt_mem i

private theorem nelt_mem (i : (Fin 3 × Fin 3) × (Fin 8 × Fin 2)) :
    nelt i ∈ firstModel := by
  exact firstModel.mul_mem
    (firstModel.mul_mem (pelt_mem i.1) (firstModel.pow_mem (c_word ▸ word_mem _) _))
    (firstModel.pow_mem (d_word ▸ word_mem _) _)

private theorem nelt_normalizes (i : (Fin 3 × Fin 3) × (Fin 8 × Fin 2)) :
    nelt i ∈ normalizer (nine : Set (Equiv.Perm (Fin 22))) := by
  exact (normalizer _).mul_mem
    ((normalizer _).mul_mem (nine.le_normalizer ⟨i.1, rfl⟩)
      ((normalizer _).pow_mem (normalizes_of_pelt c c_normalizes) _))
    ((normalizer _).pow_mem (normalizes_of_pelt d d_normalizes) _)

/-- An explicit subgroup of order nine in the first candidate has at least
144 elements in its relative normalizer. The four generators and all finite
multiplication, conjugation, and distinctness checks are kernel certificates. -/
public theorem firstModel_large_three_normalizer :
    ∃ P : Subgroup firstModel, Nat.card P = 9 ∧
      144 ≤ Nat.card (normalizer (P : Set firstModel)) := by
  let P := nine.subgroupOf firstModel
  refine ⟨P, ?_, ?_⟩
  · exact (Nat.card_congr (subgroupOfEquivOfLe nine_le).toEquiv).trans nine_card
  · let f : ((Fin 3 × Fin 3) × (Fin 8 × Fin 2)) → normalizer (P : Set firstModel) :=
      fun i => ⟨⟨nelt i, nelt_mem i⟩, by
        rw [← subgroupOf_normalizer_eq nine_le]
        exact nelt_normalizes i⟩
    have hf : Function.Injective f := by
      intro i j h
      apply nelt_inj_points
      have he : nelt i = nelt j := congrArg (fun x : normalizer (P : Set firstModel) =>
        ((x : firstModel) : Equiv.Perm (Fin 22))) h
      exact congrArg (fun g : Equiv.Perm (Fin 22) => (g 1, g 3, g 4)) he
    simpa using Nat.card_le_card_of_injective f hf

/-- A relabeling identifying the two rejected candidates. -/
@[expose] public def thirdRelabeling : Equiv.Perm (Fin 22) :=
  List.formPerm [1,7,5,2,3,10,4,6,9,8] *
    List.formPerm [12,18,16,13,14,21,15,17,20,19]

private theorem thirdRelabeling_ell :
    (MulAut.conj thirdRelabeling) ell = ell ^ 7 := by decide +kernel
private theorem thirdRelabeling_m :
    (MulAut.conj thirdRelabeling) m = m := by decide +kernel
private theorem thirdRelabeling_n1 :
    (MulAut.conj thirdRelabeling) n1 = n3 := by decide +kernel

/-- The rejected third candidate is conjugate to the first. -/
public theorem map_firstModel_eq_thirdModel :
    firstModel.map (MulAut.conj thirdRelabeling).toMonoidHom = thirdModel := by
  let f := (MulAut.conj thirdRelabeling).toMonoidHom
  have hl : ell ∈ firstModel := subset_closure (by simp)
  have hm : m ∈ firstModel := subset_closure (by simp)
  have hn : n1 ∈ firstModel := subset_closure (by simp)
  have hl' : ell ^ 7 ∈ firstModel.map f := thirdRelabeling_ell ▸ mem_map_of_mem f hl
  have hm' : m ∈ firstModel.map f := thirdRelabeling_m ▸ mem_map_of_mem f hm
  have hn' : n3 ∈ firstModel.map f := thirdRelabeling_n1 ▸ mem_map_of_mem f hn
  have hl8 : (ell ^ 7) ^ 8 = ell := by decide +kernel
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    rw [firstModel, closure_le]
    intro g hg
    change (MulAut.conj thirdRelabeling) g ∈ thirdModel
    rcases hg with rfl | rfl | rfl
    · rw [thirdRelabeling_ell]
      exact thirdModel.pow_mem (subset_closure (by simp)) _
    · rw [thirdRelabeling_m]
      exact subset_closure (by simp)
    · rw [thirdRelabeling_n1]
      exact subset_closure (by simp)
  · rw [thirdModel, closure_le]
    intro g hg
    change g ∈ firstModel.map f
    rcases hg with rfl | rfl | rfl
    · exact hl8 ▸ (firstModel.map f).pow_mem hl' 8
    · exact hm'
    · exact hn'

/-- An actual equivalence between the two rejected permutation groups. -/
public noncomputable def firstEquivThird : firstModel ≃* thirdModel :=
  ((MulAut.conj thirdRelabeling).subgroupMap firstModel).trans
    (MulEquiv.subgroupCongr map_firstModel_eq_thirdModel)

universe u v
variable {G : Type u} [Group G] [Finite G]

/-- An order-nine subgroup of an embedded finite group maps to a Sylow
three-subgroup of a group of order 443520. Its normalizer therefore has
order at most the given Sylow-normalizer order, 72. -/
public theorem normalizer_card_le_of_embedding
    (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    {K : Type v} [Group K] [Finite K] (f : K →* G) (hf : Function.Injective f)
    (P : Subgroup K) (hP : Nat.card P = 9) :
    Nat.card (normalizer (P : Set K)) ≤ 72 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hmap : Nat.card (P.map f) = 3 ^ (Nat.card G).factorization 3 := by
    rw [card_map_of_injective hf, hP, hcard]
    decide +kernel
  let S : Sylow 3 G := Sylow.ofCard (P.map f) hmap
  have hN : Nat.card (normalizer (P.map f : Set G)) = 72 := hN3 S
  have hb := card_le_of_le (P.le_normalizer_map f)
  rwa [card_map_of_injective hf, hN] at hb

/-- The first candidate cannot embed under the source order and normalizer
hypotheses. No abstract M11 identification is used. -/
public theorem firstModel_not_embed
    (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    (f : firstModel →* G) : ¬ Function.Injective f := by
  intro hf
  obtain ⟨P, hP, hlarge⟩ := firstModel_large_three_normalizer
  have hsmall := normalizer_card_le_of_embedding hcard hN3 f hf P hP
  omega

private theorem injective_comp_equiv {A B C : Type*} [Group A] [Group B] [Group C]
    (f : B →* C) (e : A ≃* B) (hf : Function.Injective f) :
    Function.Injective (f.comp e.toMonoidHom) := by
  intro x y h
  exact e.injective (hf h)

/-- The same obstruction excludes the third candidate via its checked
conjugacy with the first. -/
public theorem thirdModel_not_embed
    (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    (f : thirdModel →* G) : ¬ Function.Injective f := by
  intro hf
  exact firstModel_not_embed hcard hN3 (f.comp firstEquivThird.toMonoidHom)
    (injective_comp_equiv f firstEquivThird hf)

end Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification
