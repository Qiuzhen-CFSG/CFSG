module

public import Theory.Representation.BinaryOffender.Basic
public import Theory.ElementaryAbelian.BinaryQuotientRank
public import Mathlib.Data.ENat.Lattice

/-!
# The module parameters of E.3

The parameter `moduleM` is the minimum of involution fixed-space codimensions.
We include the dimension of the module in the minimizing set: this makes the
set nonempty and implements the odd-order convention. Every involution
codimension is at most that dimension, so the extra entry does not change the
minimum when involutions exist.

`fixedSpaceFamily` is the actual family in E.3.8, using relative subgroup index
for codimension. `moduleA` is its supremum in the extended naturals, so an empty
family gives zero without concealing an unproved existence assertion.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
manuscript (1 March 2004), E.3.1–2 and E.3.8–9, printed pp. 231–232.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE

open Representation.BinaryOffender
open scoped IsMulCommutative

variable {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]

/-- E.3.1, with the dimension as an explicit fallback for the empty family. -/
noncomputable def moduleM (ρ : Representation (ZMod 2) X W) : ℕ :=
  sInf (insert (Module.finrank (ZMod 2) W)
    {n | ∃ t : X, orderOf t = 2 ∧ fixedCodim ρ (Subgroup.zpowers t) = n})

/-- E.3.8: equality of fixed spaces on every subgroup of codimension below `k`. -/
def fixedSpaceFamily (ρ : Representation (ZMod 2) X W) (k : ℕ) :
    Set (Subgroup X) :=
  {A | 0 < k ∧ IsElementaryTwo A ∧
    ∀ B ≤ A, Nat.log 2 (B.relIndex A) < k → fixedSpace ρ A = fixedSpace ρ B}

/-- E.3.9, as an extended supremum; finiteness is a separate theorem. -/
noncomputable def moduleA (ρ : Representation (ZMod 2) X W) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : (fixedSpaceFamily ρ k).Nonempty), (k : ℕ∞)

theorem moduleM_le_dimension (ρ : Representation (ZMod 2) X W) :
    moduleM ρ ≤ Module.finrank (ZMod 2) W :=
  csInf_le' (Set.mem_insert _ _)

theorem moduleM_le_involution (ρ : Representation (ZMod 2) X W)
    {t : X} (ht : orderOf t = 2) :
    moduleM ρ ≤ fixedCodim ρ (Subgroup.zpowers t) :=
  csInf_le' (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩)

theorem moduleM_eq_dimension_of_no_involution (ρ : Representation (ZMod 2) X W)
    (h : ¬ ∃ t : X, orderOf t = 2) :
    moduleM ρ = Module.finrank (ZMod 2) W := by
  apply le_antisymm (moduleM_le_dimension ρ)
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro n (rfl | ⟨t, ht, _⟩)
  · exact le_rfl
  · exact (h ⟨t, ht⟩).elim

/-- The odd-order clause of E.3.1. -/
theorem moduleM_eq_dimension_of_odd [Finite X]
    (ρ : Representation (ZMod 2) X W) (h : Odd (Nat.card X)) :
    moduleM ρ = Module.finrank (ZMod 2) W := by
  apply moduleM_eq_dimension_of_no_involution ρ
  rintro ⟨t, ht⟩
  exact h.not_two_dvd_nat (ht ▸ orderOf_dvd_natCard t)

theorem fixedSpace_antitone (ρ : Representation (ZMod 2) X W)
    {A B : Subgroup X} (h : A ≤ B) : fixedSpace ρ B ≤ fixedSpace ρ A := by
  intro w hw
  change ∀ a : A, ρ (a : X) w = w
  intro a
  change ∀ b : B, ρ (b : X) w = w at hw
  exact hw ⟨a, h a.property⟩

theorem fixedCodim_mono [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) {A B : Subgroup X} (h : A ≤ B) :
    fixedCodim ρ A ≤ fixedCodim ρ B := by
  have hdim := Submodule.finrank_mono (fixedSpace_antitone ρ h)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  omega

/-- E.3.2, for any binary action; faithfulness is not needed for this inequality. -/
theorem moduleM_le_fixedCodim [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) {A : Subgroup X} (hA : IsElementaryTwo A) :
    moduleM ρ ≤ fixedCodim ρ A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t, htA, ht⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t htA) ht
  exact (moduleM_le_involution ρ ht2).trans
    (fixedCodim_mono ρ ((Subgroup.zpowers_le).mpr htA))

/-- With an involution present, the minimum really is an involution codimension. -/
theorem moduleM_attained [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (h : ∃ t : X, orderOf t = 2) :
    ∃ t : X, orderOf t = 2 ∧ fixedCodim ρ (Subgroup.zpowers t) = moduleM ρ := by
  have hm : moduleM ρ ∈ insert (Module.finrank (ZMod 2) W)
      {n | ∃ t : X, orderOf t = 2 ∧ fixedCodim ρ (Subgroup.zpowers t) = n} :=
    csInf_mem ⟨_, Set.mem_insert _ _⟩
  rcases hm with hm | hm
  · obtain ⟨t, ht⟩ := h
    refine ⟨t, ht, le_antisymm ?_ (moduleM_le_involution ρ ht)⟩
    rw [hm]
    have := fixedCodim_add_finrank ρ (Subgroup.zpowers t)
    omega
  · exact hm

/-- In even order, Cauchy's theorem supplies a minimizing involution. -/
theorem moduleM_attained_of_even [Finite X] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (h : Even (Nat.card X)) :
    ∃ t : X, orderOf t = 2 ∧ fixedCodim ρ (Subgroup.zpowers t) = moduleM ρ :=
  moduleM_attained ρ (exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h))

theorem le_moduleA_of_mem (ρ : Representation (ZMod 2) X W)
    {k : ℕ} {A : Subgroup X} (hA : A ∈ fixedSpaceFamily ρ k) :
    (k : ℕ∞) ≤ moduleA ρ :=
  le_iSup_of_le k (le_iSup_of_le ⟨A, hA⟩ le_rfl)

/-- The families decrease with their positive integer parameter. -/
theorem fixedSpaceFamily_mono (ρ : Representation (ZMod 2) X W)
    {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    fixedSpaceFamily ρ k ⊆ fixedSpaceFamily ρ j := by
  rintro A ⟨_, hA, h⟩
  exact ⟨hj, hA, fun B hBA hB => h B hBA (hB.trans_le hjk)⟩

/-- Faithfulness turns a full fixed space into a trivial acting subgroup. -/
theorem fixedSpace_eq_top_iff (ρ : Representation (ZMod 2) X W)
    (hρ : Function.Injective ρ) (A : Subgroup X) :
    fixedSpace ρ A = ⊤ ↔ A = ⊥ := by
  constructor
  · intro h
    apply le_antisymm ?_ bot_le
    intro a ha
    apply Subgroup.mem_bot.mpr
    apply hρ
    ext w
    have hw : w ∈ fixedSpace ρ A := h ▸ Submodule.mem_top
    change ∀ b : A, ρ (b : X) w = w at hw
    simpa using hw ⟨a, ha⟩
  · rintro rfl
    exact fixedSpace_bot ρ

/-- Nontrivial subgroups have positive fixed-space codimension in a faithful action. -/
theorem fixedCodim_pos [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ)
    {A : Subgroup X} (hA : A ≠ ⊥) : 0 < fixedCodim ρ A := by
  by_contra h
  have hzero : fixedCodim ρ A = 0 := by omega
  have hdim := fixedCodim_add_finrank ρ A
  have htop : fixedSpace ρ A = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  exact hA ((fixedSpace_eq_top_iff ρ hρ A).mp htop)

/-- The positivity observation following E.3.1. -/
theorem moduleM_pos [FiniteDimensional (ZMod 2) W] [Nontrivial W]
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ) :
    0 < moduleM ρ := by
  apply Nat.lt_of_succ_le
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro n (rfl | ⟨t, ht, rfl⟩)
  · exact Module.finrank_pos
  · apply fixedCodim_pos ρ hρ
    intro hz
    have ht1 : t = 1 := Subgroup.mem_bot.mp (hz ▸ Subgroup.mem_zpowers t)
    simp [ht1] at ht

/-- The observation following E.3.8: `A₁` consists of all nontrivial
 elementary abelian two-subgroups. -/
theorem mem_fixedSpaceFamily_one_iff [Finite X]
    (ρ : Representation (ZMod 2) X W) (A : Subgroup X) :
    A ∈ fixedSpaceFamily ρ 1 ↔ IsElementaryTwo A := by
  constructor
  · exact fun h => h.2.1
  · intro hA
    refine ⟨by decide, hA, ?_⟩
    intro B hBA hB
    have hzero : Nat.log 2 (B.relIndex A) = 0 := by omega
    have hlt : B.relIndex A < 2 := (Nat.log_eq_zero_iff.mp hzero).resolve_right (by omega)
    have hpos : B.relIndex A ≠ 0 := by
      intro hz
      have hdvd := B.relIndex_dvd_card A
      rw [hz, zero_dvd_iff] at hdvd
      exact Nat.card_pos.ne' hdvd
    have hidx : B.relIndex A = 1 := by omega
    have heq := le_antisymm hBA (Subgroup.relIndex_eq_one.mp hidx)
    rw [heq]

/-- A member cannot tolerate removal of its entire rank: the trivial subgroup
 fixes the whole module. -/
theorem parameter_le_rank_of_mem_fixedSpaceFamily
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ)
    {k : ℕ} {A : Subgroup X} (hA : A ∈ fixedSpaceFamily ρ k) : k ≤ rank A := by
  by_contra h
  have heq := hA.2.2 ⊥ bot_le (by simpa [rank] using Nat.lt_of_not_ge h)
  rw [fixedSpace_bot] at heq
  exact hA.2.1.1 ((fixedSpace_eq_top_iff ρ hρ A).mp heq)

/-- The extended supremum defining `a` is finite for a faithful finite action. -/
theorem moduleA_le_log_card [Finite X]
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ) :
    moduleA ρ ≤ (Nat.log 2 (Nat.card X) : ℕ∞) := by
  apply iSup_le
  intro k
  apply iSup_le
  rintro ⟨A, hA⟩
  apply ENat.natCast_le_natCast.mpr
  exact (parameter_le_rank_of_mem_fixedSpaceFamily ρ hρ hA).trans
    (Nat.log_mono_right A.card_le_card_group)

theorem moduleA_ne_top [Finite X]
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ) :
    moduleA ρ ≠ ⊤ := ne_top_of_le_ne_top (by simp) (moduleA_le_log_card ρ hρ)

/-- The odd-order clause of E.3.9. -/
theorem moduleA_eq_zero_of_odd [Finite X]
    (ρ : Representation (ZMod 2) X W) (h : Odd (Nat.card X)) : moduleA ρ = 0 := by
  apply le_antisymm _ _root_.bot_le
  apply iSup_le
  intro k
  apply iSup_le
  rintro ⟨A, hA⟩
  let _ : IsElementaryAbelian 2 A := hA.2.1.2
  obtain ⟨t, htA, ht⟩ := A.bot_or_exists_ne_one.resolve_left hA.2.1.1
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t htA) ht
  exact (h.not_two_dvd_nat (ht2 ▸ orderOf_dvd_natCard t)).elim

/-- In even order the first family is nonempty, by Cauchy's theorem. -/
theorem fixedSpaceFamily_one_nonempty_of_even [Finite X]
    (ρ : Representation (ZMod 2) X W) (h : Even (Nat.card X)) :
    (fixedSpaceFamily ρ 1).Nonempty := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (even_iff_two_dvd.mp h)
  refine ⟨Subgroup.zpowers t, (mem_fixedSpaceFamily_one_iff ρ _).mpr ⟨?_, ?_⟩⟩
  · intro hz
    have ht1 : t = 1 := Subgroup.mem_bot.mp (hz ▸ Subgroup.mem_zpowers t)
    simp [ht1] at ht
  · exact IsElementaryAbelian.zpowers_of_pow_eq_one ((orderOf_eq_prime_iff.mp ht).1)

/-- For a faithful finite action, whenever the families are nonempty their
supremum is a maximum. This is the maximum convention in E.3.9. -/
theorem moduleA_attained [Finite X]
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ)
    (h : ∃ k, (fixedSpaceFamily ρ k).Nonempty) :
    ∃ k, (fixedSpaceFamily ρ k).Nonempty ∧ moduleA ρ = (k : ℕ∞) := by
  let S : Set ℕ := {k | (fixedSpaceFamily ρ k).Nonempty}
  have hbound : S ⊆ Set.Iic (Nat.log 2 (Nat.card X)) := by
    rintro k ⟨A, hA⟩
    exact (parameter_le_rank_of_mem_fixedSpaceFamily ρ hρ hA).trans
      (Nat.log_mono_right A.card_le_card_group)
  obtain ⟨k, hk, hmax⟩ := Set.exists_max_image S id
    ((Set.finite_Iic _).subset hbound) h
  refine ⟨k, hk, le_antisymm ?_ ?_⟩
  · apply iSup_le
    intro j
    apply iSup_le
    intro hj
    exact_mod_cast hmax j hj
  · obtain ⟨A, hA⟩ := hk
    exact le_moduleA_of_mem ρ hA

/-- In even order `a` is the maximum positive parameter occurring in E.3.8. -/
theorem moduleA_attained_of_even [Finite X]
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ)
    (h : Even (Nat.card X)) :
    ∃ k, (fixedSpaceFamily ρ k).Nonempty ∧ moduleA ρ = (k : ℕ∞) :=
  moduleA_attained ρ hρ ⟨1, fixedSpaceFamily_one_nonempty_of_even ρ h⟩

end CFSG.Quasithin.ChapterE
