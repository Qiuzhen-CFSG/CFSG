module
public import Theory.Representation.BinaryOffender.FlagCodimension
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.Replacement
public import Mathlib.Data.ENNReal.BigOperators
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections

/-!
# Dimension descent and constituent ratio bounds for B.5.1

A flag section is the literal quotient of one invariant subspace by its
predecessor. Rank-nullity proves strict descent whenever the flag has another
nonzero selected factor. Fixed codimensions telescope without splitting any
extension. Dividing by the same actor rank gives the sum of action ratios.

For a minimal best offender, quadratic replacement and faithfulness on each
section compare these ratios with the quadratic ratios of the actual action
images. The genuine B.1.5(8) group theorem supplies that faithfulness when the
generalized Fitting subgroup is quasisimple and the two-core is trivial.
`quasisimple_flag_estimates` proves the complete numerical conclusion (+),
including attainment of its minimum and strict dimension descent. It does not
assert that arbitrary chief factors are natural or that extensions split.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the inequality
(*) and conclusion (+) in B.5.1, printed p.100.
-/

@[expose] public section
open Representation Representation.BinaryOffender
open scoped BigOperators ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

noncomputable abbrev sectionDimension (U W : Subrepresentation ρ) : ℕ :=
  Module.finrank (ZMod 2) (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule)

/-- Quotienting by an actual nonzero invariant subspace strictly lowers the
dimension used in the induction, regardless of whether the extension splits. -/
theorem quotient_finrank_lt (W : Subrepresentation ρ) (hW : W.toSubmodule ≠ ⊥) :
    Module.finrank (ZMod 2) (V ⧸ W.toSubmodule) < Module.finrank (ZMod 2) V := by
  have hd := W.toSubmodule.finrank_quotient_add_finrank
  have hn : Module.finrank (ZMod 2) W.toSubmodule ≠ 0 :=
    fun h => hW (Submodule.finrank_eq_zero.mp h)
  omega

theorem sectionDimension_add (U W : Subrepresentation ρ) (hUW : U ≤ W) :
    sectionDimension ρ U W + Module.finrank (ZMod 2) U.toSubmodule =
      Module.finrank (ZMod 2) W.toSubmodule := by
  have h := (sectionLower ρ U W).toSubmodule.finrank_quotient_add_finrank
  rw [(sectionLowerEquiv ρ hUW).finrank_eq] at h
  exact h

theorem sectionDimension_pos (U W : Subrepresentation ρ) (hUW : U < W) :
    0 < sectionDimension ρ U W := by
  have hd := sectionDimension_add ρ U W hUW.le
  have hl : U.toSubmodule < W.toSubmodule := hUW
  have hf := Submodule.finrank_lt_finrank_of_lt hl
  omega

theorem sum_sectionDimension_le (c : ℕ → Subrepresentation ρ) (hc : Monotone c)
    (n : ℕ) :
    ∑ i ∈ Finset.range n, sectionDimension ρ (c i) (c (i + 1)) ≤
      Module.finrank (ZMod 2) V := by
  have h (m : ℕ) :
      ∑ i ∈ Finset.range m, sectionDimension ρ (c i) (c (i + 1)) ≤
        Module.finrank (ZMod 2) (c m).toSubmodule := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have := sectionDimension_add ρ (c m) (c (m + 1)) (hc (Nat.le_succ m))
      omega
  exact (h n).trans (c n).toSubmodule.finrank_le

theorem sectionDimension_lt_of_second_factor (c : ℕ → Subrepresentation ρ)
    (hc : Monotone c) (n : ℕ) {i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) (hstrict : c j < c (j + 1)) :
    sectionDimension ρ (c i) (c (i + 1)) < Module.finrank (ZMod 2) V := by
  classical
  have hsub : ({i, j} : Finset ℕ) ⊆ Finset.range n := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_range.mpr hi
    · exact Finset.mem_range.mpr hj
  have hp := Finset.sum_le_sum_of_subset
    (f := fun k => sectionDimension ρ (c k) (c (k + 1))) hsub
  rw [Finset.sum_pair hij] at hp
  have ht := sum_sectionDimension_le ρ c hc n
  have hjpos := sectionDimension_pos ρ (c j) (c (j + 1)) hstrict
  omega

theorem sum_actionRatio_flag_le (c : ℕ → Subrepresentation ρ) (hc : Monotone c)
    (n : ℕ) (A : Subgroup G) :
    ∑ i ∈ Finset.range n, actionRatio (sectionRepresentation ρ (c i) (c (i + 1))) A ≤
      actionRatio ρ A := by
  simp only [actionRatio, div_eq_mul_inv, ← Finset.sum_mul]
  apply mul_le_mul' _ le_rfl
  exact_mod_cast sum_fixedCodim_flag_le ρ c hc n A

variable [Finite G]

omit [FiniteDimensional (ZMod 2) V] [Finite G] in
theorem image_quadraticRatio_le_actionRatio (A : Subgroup G) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A)
    (hf : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1) :
    quadraticRatio (imageRepresentation ρ) ≤ actionRatio ρ A := by
  have he := hA.actionSubgroup ρ hf
  have hqi : IsQuadratic (imageRepresentation ρ) (actionSubgroup ρ A) := by
    rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ v
    exact hq x hx y hy v
  have hl : quadraticRatio (imageRepresentation ρ) ≤
      actionRatio (imageRepresentation ρ) (actionSubgroup ρ A) :=
    iInf_le_of_le _ (iInf_le_of_le ⟨he, hqi⟩ le_rfl)
  simpa only [actionRatio, fixedCodim_actionSubgroup, actionSubgroup_rank ρ A hf] using hl

theorem sum_section_image_quadraticRatio_le_one
    (c : ℕ → Subrepresentation ρ) (hc : Monotone c) (n : ℕ)
    (I : Finset ℕ) (hI : I ⊆ Finset.range n) (A : Subgroup G)
    (hA : IsMinimalBestOffender ρ A)
    (hf : ∀ i ∈ I, ∀ a ∈ A,
      (∀ v, sectionRepresentation ρ (c i) (c (i + 1)) a v = v) → a = 1) :
    ∑ i ∈ I, quadraticRatio
      (imageRepresentation (sectionRepresentation ρ (c i) (c (i + 1)))) ≤ 1 := by
  have hq := hA.isQuadratic ρ
  calc
    _ ≤ ∑ i ∈ I, actionRatio (sectionRepresentation ρ (c i) (c (i + 1))) A := by
      apply Finset.sum_le_sum
      intro i hi
      exact image_quadraticRatio_le_actionRatio _ A hA.1.1
        (quadratic_section ρ _ _ hq) (hf i hi)
    _ ≤ ∑ i ∈ Finset.range n,
        actionRatio (sectionRepresentation ρ (c i) (c (i + 1))) A :=
      Finset.sum_le_sum_of_subset hI
    _ ≤ actionRatio ρ A := sum_actionRatio_flag_le ρ c hc n A
    _ ≤ 1 := (actionRatio_le_one_iff ρ hA.1.1).mpr (hA.1.isOffender ρ).2


theorem quadraticRatio_pos_of_faithful (hf : Function.Injective ρ) :
    0 < quadraticRatio ρ := by
  classical
  have hpos (A : Subgroup G) (hA : IsElementaryTwo A) : 0 < actionRatio ρ A := by
    have hd : fixedCodim ρ A ≠ 0 := by
      intro hd
      have hfix := (fixedCodim_eq_zero_iff ρ A).mp hd
      apply hA.1
      apply le_antisymm _ bot_le
      intro a ha
      apply hf
      ext v
      have hv : v ∈ fixedSpace ρ A := by rw [hfix]; trivial
      simpa using hv ⟨a, ha⟩
    exact ENNReal.div_pos (by exact_mod_cast hd) (by simp)
  let S := {A : Subgroup G // IsElementaryTwo A ∧ IsQuadratic ρ A}
  by_cases hs : Nonempty S
  · let : Nonempty S := hs
    obtain ⟨A, hmin⟩ := exists_eq_ciInf_of_finite (f := fun A : S => actionRatio ρ A.val)
    rw [iInf_subtype] at hmin
    rw [quadraticRatio, ← hmin]
    exact hpos A.val A.property.1
  · have ht : quadraticRatio ρ = ⊤ := by
      apply iInf_eq_top.mpr
      intro A
      apply iInf_eq_top.mpr
      intro hA
      exact (hs ⟨⟨A, hA⟩⟩).elim
    rw [ht]
    exact ENNReal.zero_lt_top

omit [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Finite G] in
theorem ratio_pair_le_one {I : Finset ℕ} {q : ℕ → ℝ≥0∞}
    (hbudget : ∑ i ∈ I, q i ≤ 1) {i j : ℕ} (hi : i ∈ I) (hj : j ∈ I)
    (hne : i ≠ j) : q i + q j ≤ 1 := by
  classical
  have hsub : ({i, j} : Finset ℕ) ⊆ I := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  have h := Finset.sum_le_sum_of_subset (f := q) hsub
  rw [Finset.sum_pair hne] at h
  exact h.trans hbudget

omit [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Finite G] in
theorem ratio_lt_one_of_second_positive {I : Finset ℕ} {q : ℕ → ℝ≥0∞}
    (hbudget : ∑ i ∈ I, q i ≤ 1) {i j : ℕ} (hi : i ∈ I) (hj : j ∈ I)
    (hne : i ≠ j) (hpos : 0 < q j) : q i < 1 := by
  have hp := ratio_pair_le_one hbudget hi hj hne
  have hi1 : q i ≤ 1 := le_trans le_self_add hp
  exact (ENNReal.lt_add_right (ne_top_of_le_ne_top (by simp) hi1)
    (ne_of_gt hpos)).trans_le hp

omit [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Finite G] in
theorem exists_le_reciprocal_card_of_ratio_sum {I : Finset ℕ} (hI : I.Nonempty)
    {q : ℕ → ℝ≥0∞} (hbudget : ∑ i ∈ I, q i ≤ 1) :
    ∃ k ∈ I, (∀ i ∈ I, q k ≤ q i) ∧ q k ≤ 1 / (I.card : ℝ≥0∞) := by
  obtain ⟨k, hk, hmin⟩ := I.exists_min_image q hI
  refine ⟨k, hk, hmin, ?_⟩
  have hsum : (I.card : ℝ≥0∞) * q k ≤ ∑ i ∈ I, q i := by
    calc
      _ = ∑ _i ∈ I, q k := by simp
      _ ≤ _ := Finset.sum_le_sum hmin
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hI.ne_empty)) (Or.inl (by simp))).mpr
  simpa [mul_comm] using hsum.trans hbudget


/-- The complete numerical conclusion (+) for a selected family of genuine
noncentral invariant sections, together with the strict dimension descent. -/
theorem quasisimple_flag_estimates
    (hfaith : Function.Injective ρ)
    (hL : Theory.GroupTheory.IsQuasisimple (Theory.GroupTheory.generalizedFitting G))
    (hcore : pCore 2 G = ⊥)
    (c : ℕ → Subrepresentation ρ) (hc : Monotone c) (n : ℕ)
    (I : Finset ℕ) (hI : I ⊆ Finset.range n) (hr : 1 < I.card)
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hnoncentral : ∀ i ∈ I,
      subspaceCommutator (sectionRepresentation ρ (c i) (c (i + 1))) ⊤
        (Theory.GroupTheory.generalizedFitting G) ≠ ⊥) :
    let q := fun i => quadraticRatio
      (imageRepresentation (sectionRepresentation ρ (c i) (c (i + 1))))
    (∀ i ∈ I, sectionDimension ρ (c i) (c (i + 1)) < Module.finrank (ZMod 2) V) ∧
    (∑ i ∈ I, q i ≤ 1) ∧
    (∀ i ∈ I, 0 < q i ∧ q i < 1) ∧
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → q i + q j ≤ 1) ∧
    ∃ k ∈ I, (∀ i ∈ I, q k ≤ q i) ∧ q k ≤ 1 / (I.card : ℝ≥0∞) ∧
      1 / (I.card : ℝ≥0∞) ≤ 1 / 2 := by
  dsimp only
  let q := fun i => quadraticRatio
    (imageRepresentation (sectionRepresentation ρ (c i) (c (i + 1))))
  have hfaithA : ∀ i ∈ I, ∀ a ∈ A,
      (∀ v, sectionRepresentation ρ (c i) (c (i + 1)) a v = v) → a = 1 := by
    intro i hi
    exact (source_lemma_B_1_5_8 ρ hfaith hA.1 hL hcore (hc (Nat.le_succ i))
      (hnoncentral i hi)).1
  have hsum : ∑ i ∈ I, q i ≤ 1 :=
    sum_section_image_quadraticRatio_le_one ρ c hc n I hI A hA hfaithA
  have hpos (i : ℕ) : 0 < q i :=
    quadraticRatio_pos_of_faithful _ (imageRepresentation_injective _)
  have hstrict (i : ℕ) (hi : i ∈ I) : c i < c (i + 1) := by
    have hnon := hnoncentral i hi
    let σ := sectionRepresentation ρ (c i) (c (i + 1))
    let M := subspaceCommutator σ ⊤ (Theory.GroupTheory.generalizedFitting G)
    have : Nontrivial M := (Submodule.nontrivial_iff_ne_bot).mpr hnon
    have : Nontrivial ((c (i + 1)).toSubmodule ⧸
        (sectionLower ρ (c i) (c (i + 1))).toSubmodule) :=
      Function.Injective.nontrivial (M.subtype_injective)
    have hp : 0 < sectionDimension ρ (c i) (c (i + 1)) := Module.finrank_pos
    refine lt_of_le_of_ne (hc (Nat.le_succ i)) ?_
    intro he
    have hd := sectionDimension_add ρ (c i) (c (i + 1)) (hc (Nat.le_succ i))
    rw [he] at hd
    have hz := sectionDimension_add ρ (c (i + 1)) (c (i + 1)) le_rfl
    rw [he] at hp
    omega
  refine ⟨?_, hsum, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hr i
    exact sectionDimension_lt_of_second_factor ρ c hc n
      (Finset.mem_range.mp (hI hi)) (Finset.mem_range.mp (hI hj)) hji.symm (hstrict j hj)
  · intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hr i
    exact ⟨hpos i, ratio_lt_one_of_second_positive hsum hi hj hji.symm (hpos j)⟩
  · intro i hi j hj hij
    exact ratio_pair_le_one hsum hi hj hij
  · have hne : I.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨k, hk, hmin, hkq⟩ := exists_le_reciprocal_card_of_ratio_sum hne hsum
    refine ⟨k, hk, hmin, hkq, ?_⟩
    apply ENNReal.div_le_div_left
    exact_mod_cast (show 2 ≤ I.card by omega)

end CFSG.Quasithin.ChapterB.QuasisimpleSource
