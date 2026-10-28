module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Residual
public import Mathlib.LinearAlgebra.Dimension.Free
public import Theory.Representation.BinaryOffender.SubspaceAction
/-!
# Planes of pair vectors in the seven-letter core

Three nonzero pair vectors in a binary plane are the three edges of one
triple. The plane is the even core on that triple, equivalently the
complementary plane of its weight-four complement. Its stabilizer contains
an elementary nine-group, supplied by the actual weight-four stabilizer.

Source: Aschbacher–Smith, 13.7.6(3b), printed p.939.
-/
@[expose] public section
namespace BinaryPermutation.SevenTriangle
open SevenParabolic Module
abbrev Ω := Fin 7

def pair (i j : Ω) : Space :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib]
    decide⟩

/-- Distinct letters give a weight-two vector in the literal even core. -/
theorem pair_weight (i j : Ω) (hij : i ≠ j) : weight (pair i j) = 2 := by
  have hc : ∀ i j : Ω, i ≠ j → weight (pair i j) = 2 := by decide +kernel
  exact hc i j hij

private theorem pair_of_weight_two (v : Space) (hv : weight v = 2) :
    ∃ i j : Ω, i ≠ j ∧ v = pair i j := by
  have hc : ∀ v : Ω → ZMod 2,
      (Finset.univ.filter (fun i => v i ≠ 0)).card = 2 →
      ∃ i j : Ω, i ≠ j ∧ v = Pi.single i 1 + Pi.single j 1 := by decide +kernel
  obtain ⟨i,j,hij,h⟩ := hc v.val hv
  exact ⟨i,j,hij,Subtype.ext h⟩

private theorem edges_meet (i j k l : Ω) (hij : i ≠ j) (hkl : k ≠ l)
    (hs : weight (pair i j + pair k l) = 2) : i = k ∨ i = l ∨ j = k ∨ j = l := by
  by_contra hn
  push Not at hn
  have hsupport : Finset.univ.filter (fun a => (pair i j + pair k l).val a ≠ 0) = {i,j,k,l} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, pair, Submodule.coe_add, Pi.add_apply, Pi.single_apply]
    by_cases hai : a = i
    · subst a; simp [hij, hn.1, hn.2.1]
    by_cases haj : a = j
    · subst a; simp [hij.symm, hn.2.2.1, hn.2.2.2]
    by_cases hak : a = k
    · subst a; simp [hn.1.symm, hn.2.2.1.symm, hkl]
    by_cases hal : a = l
    · subst a; simp [hn.2.1.symm, hn.2.2.2.symm, hkl.symm]
    simp [hai,haj,hak,hal]
  change (Finset.univ.filter _).card = 2 at hs
  rw [hsupport] at hs
  simp [hij, hkl, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2] at hs

private theorem pair_comm (i j : Ω) : pair i j = pair j i := by
  apply Subtype.ext
  exact add_comm _ _

private theorem edges_triangle (u v : Space)
    (hu : weight u = 2) (hv : weight v = 2) (hs : weight (u+v) = 2) :
    ∃ i j k : Ω, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ u = pair i j ∧ v = pair i k := by
  obtain ⟨i,j,hij,rfl⟩ := pair_of_weight_two u hu
  obtain ⟨k,l,hkl,rfl⟩ := pair_of_weight_two v hv
  have hne : pair i j ≠ pair k l := by
    intro h
    rw [h, ZModModule.add_self] at hs
    have : weight (0 : Space) = 0 := by decide
    omega
  rcases edges_meet i j k l hij hkl hs with h | h | h | h
  · subst k
    exact ⟨i,j,l,hij,hkl,fun h => hne (h ▸ rfl),rfl,rfl⟩
  · subst l
    exact ⟨i,j,k,hij,hkl.symm,fun h => hne (h ▸ pair_comm _ _),rfl,pair_comm _ _⟩
  · subst k
    exact ⟨j,i,l,hij.symm,hkl,fun h => hne (h ▸ pair_comm _ _),pair_comm _ _,rfl⟩
  · subst l
    exact ⟨j,i,k,hij.symm,hkl.symm,fun h => hne (h ▸ rfl),pair_comm _ _,pair_comm _ _⟩

/-- A plane of pair vectors has the literal triangular basis. -/
theorem plane_basis (U : Submodule (ZMod 2) Space) (hd : finrank (ZMod 2) U = 2)
    (hu : ∀ u ∈ U, u ≠ 0 → weight u = 2) :
    ∃ i j k : Ω, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      U = Submodule.span (ZMod 2) {pair i j, pair i k} := by
  let e : U ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) := LinearEquiv.ofFinrankEq _ _ (by simp [hd])
  let a : U := e.symm ![1,0]
  let b : U := e.symm ![0,1]
  have ha : (a : Space) ≠ 0 := by
    intro h
    have he := congrArg e (show a = 0 from Subtype.ext h)
    have : (![1,0] : Fin 2 → ZMod 2) = 0 := by simp [a] at he
    exact (by decide : (![1,0] : Fin 2 → ZMod 2) ≠ 0) this
  have hb : (b : Space) ≠ 0 := by
    intro h
    have he := congrArg e (show b = 0 from Subtype.ext h)
    have : (![0,1] : Fin 2 → ZMod 2) = 0 := by simp [b] at he
    exact (by decide : (![0,1] : Fin 2 → ZMod 2) ≠ 0) this
  have hab : (a : Space) + b ≠ 0 := by
    intro h
    have he := congrArg e (show a + b = 0 from Subtype.ext h)
    have : (![1,1] : Fin 2 → ZMod 2) = 0 := by simp [a,b] at he
    exact (by decide : (![1,1] : Fin 2 → ZMod 2) ≠ 0) this
  obtain ⟨i,j,k,hij,hik,hjk,hai,hbi⟩ := edges_triangle a b
    (hu a a.property ha) (hu b b.property hb) (hu (a+b) (U.add_mem a.property b.property) hab)
  refine ⟨i,j,k,hij,hik,hjk,le_antisymm ?_ ?_⟩
  · intro w hw
    have hc : ∀ w : Fin 2 → ZMod 2,
        w = 0 ∨ w = ![1,0] ∨ w = ![0,1] ∨ w = ![1,1] := by decide
    have hw' : (⟨w,hw⟩ : U) = 0 ∨ (⟨w,hw⟩ : U) = a ∨
        (⟨w,hw⟩ : U) = b ∨ (⟨w,hw⟩ : U) = a+b := by
      rcases hc (e ⟨w,hw⟩) with h | h | h | h
      · exact Or.inl (e.injective (by simpa using h))
      · exact Or.inr (Or.inl (e.injective (by simpa [a] using h)))
      · exact Or.inr (Or.inr (Or.inl (e.injective (by simpa [b] using h))))
      · exact Or.inr (Or.inr (Or.inr (e.injective (by simpa [a,b] using h))))
    have hm₁ : (a : Space) ∈ Submodule.span (ZMod 2) {pair i j, pair i k} :=
      hai.symm ▸ Submodule.subset_span (by simp)
    have hm₂ : (b : Space) ∈ Submodule.span (ZMod 2) {pair i j, pair i k} :=
      hbi.symm ▸ Submodule.subset_span (by simp)
    rcases hw' with h | h | h | h
    · simpa only [show w = 0 from congrArg Subtype.val h] using (Submodule.zero_mem (Submodule.span (ZMod 2) {pair i j, pair i k}))
    · rw [show w = a.val from congrArg Subtype.val h]; exact hm₁
    · rw [show w = b.val from congrArg Subtype.val h]; exact hm₂
    · rw [show w = a.val + b.val from congrArg Subtype.val h]
      exact Submodule.add_mem _ hm₁ hm₂
  · apply Submodule.span_le.mpr
    intro w hw
    rcases hw with h | h
    · rw [h, ← hai]; exact a.property
    · rw [Set.mem_singleton_iff] at h
      rw [h, ← hbi]; exact b.property
/-- The triangular pair plane is the complementary even plane of one weight-four vector. -/
theorem plane_eq_plus (U : Submodule (ZMod 2) Space) (hd : finrank (ZMod 2) U = 2)
    (hu : ∀ u ∈ U, u ≠ 0 → weight u = 2) :
    ∃ v : Space, weight v = 4 ∧ U = plus v := by
  obtain ⟨i,j,k,hij,hik,hjk,hU⟩ := plane_basis U hd hu
  let s : Finset Ω := {i,j,k}
  have hsc : s.card = 3 := by simp [s,hij,hik,hjk]
  let v : Ω → ZMod 2 := fun a => if a ∈ s then 0 else 1
  have hzc : (Finset.univ.filter (fun a => a ∉ s)).card = 4 := by
    rw [← Finset.sdiff_eq_filter, Finset.card_sdiff_of_subset (Finset.subset_univ s),hsc]
    decide
  have hv : (∑ a, v a) = 0 := by
    simp only [v,Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const,
      nsmul_eq_mul, mul_one, hzc]
    decide
  have hw : (Finset.univ.filter (fun a => v a ≠ 0)).card = 4 := by
    simpa only [v,ite_ne_left_iff,ne_eq,zero_ne_one,not_false_eq_true,and_true] using hzc
  have hplus (w : Ω → ZMod 2) (hew : (∑ a,w a) = 0) :
      (∀ a, v a ≠ 0 → w a = 0) ↔ w = 0 ∨
        w = Pi.single i 1 + Pi.single j 1 ∨
        w = Pi.single i 1 + Pi.single k 1 ∨
        w = (Pi.single i 1 + Pi.single j 1) + (Pi.single i 1 + Pi.single k 1) := by
    have hzero (h : ∀ a, v a ≠ 0 → w a = 0) :
        w = Pi.single i (w i) + Pi.single j (w j) + Pi.single k (w k) := by
      funext a
      by_cases hai : a = i
      · subst a; simp [hij.symm,hik.symm]
      by_cases haj : a = j
      · subst a; simp [hij,hjk.symm]
      by_cases hak : a = k
      · subst a; simp [hik,hjk]
      have ha : a ∉ s := by simp [s,hai,haj,hak]
      rw [h a (by simp [v,ha])]
      simp [Ne.symm hai,Ne.symm haj,Ne.symm hak]
    constructor
    · intro h
      have he := hzero h
      have hc : w i + w j + w k = 0 := by
        have := congrArg (fun z : Ω → ZMod 2 => ∑ a,z a) he
        simpa [hew,Finset.sum_add_distrib] using this.symm
      have hc' : ∀ a b c : ZMod 2, a+b+c=0 →
          (a=0 ∧ b=0 ∧ c=0) ∨ (a=1 ∧ b=1 ∧ c=0) ∨
          (a=1 ∧ b=0 ∧ c=1) ∨ (a=0 ∧ b=1 ∧ c=1) := by decide
      rcases hc' (w i) (w j) (w k) hc with h | h | h | h
      · left; simpa only [h.1,h.2.1,h.2.2,Pi.single_zero,add_zero] using he
      · exact Or.inr (Or.inl (by simpa only [h.1,h.2.1,h.2.2,Pi.single_zero,add_zero] using he))
      · exact Or.inr (Or.inr (Or.inl (by simpa only [h.1,h.2.1,h.2.2,Pi.single_zero,add_zero] using he)))
      · right; right; right
        rw [he,h.1,h.2.1,h.2.2,Pi.single_zero,zero_add]
        have : (Pi.single i 1 : Ω → ZMod 2) + Pi.single i 1 = 0 := ZModModule.add_self _
        linear_combination -this
    · rintro (rfl | rfl | rfl | rfl) a ha
      · rfl
      all_goals
        have hn : a ∉ s := by
          intro hm
          simp [v,hm] at ha
        have hh : a ≠ i ∧ a ≠ j ∧ a ≠ k := by simpa [s] using hn
        simp [Ne.symm hh.1,Ne.symm hh.2.1,Ne.symm hh.2.2]
  refine ⟨⟨v,hv⟩,hw,?_⟩
  rw [hU]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro w hw
    rcases hw with h | h
    · rw [h]
      exact (hplus (pair i j).val (pair i j).property).mpr (Or.inr (Or.inl rfl))
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact (hplus (pair i k).val (pair i k).property).mpr (Or.inr (Or.inr (Or.inl rfl)))
  · intro w hw
    rcases (hplus w.val w.property).mp hw with h | h | h | h
    · have he : w = 0 := Subtype.ext h
      rw [he]; exact Submodule.zero_mem _
    · have he : w = pair i j := Subtype.ext h
      rw [he]; exact Submodule.subset_span (by simp)
    · have he : w = pair i k := Subtype.ext h
      rw [he]; exact Submodule.subset_span (by simp)
    · have he : w = pair i j + pair i k := Subtype.ext h
      rw [he]
      exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

open Subgroup Representation.BinaryOffender
/-- The actual alternating stabilizer of a pair plane has three-rank two. -/
theorem plane_stabilizer_rank (U : Submodule (ZMod 2) Space) (hd : finrank (ZMod 2) U = 2)
    (hu : ∀ u ∈ U, u ≠ 0 → weight u = 2) :
    primeRank 3 (subspaceStabilizer action U ⊓ alternatingGroup Ω : Subgroup (Equiv.Perm Ω)) = 2 := by
  obtain ⟨v,hv,rfl⟩ := plane_eq_plus U hd hu
  have hle : pointStabilizer v ≤ subspaceStabilizer action (plus v) :=
    le_subspaceStabilizer action (plus v) (fun g hg w hw => plus_invariant v g hg w hw)
  apply le_antisymm
  · exact (_root_.primeRank_le_of_injective 3
      (subspaceStabilizer action (plus v) ⊓ alternatingGroup Ω : Subgroup (Equiv.Perm Ω)).subtype
      Subtype.val_injective).trans symmetric_threeRank_le
  · have hr := pointResidual_threeRank (alternatingGroup Ω) le_rfl v hv
    apply hr.symm.le.trans
    exact (primeRank_le_of_injective 3 (pResidual 2 (alternatingGroup Ω ⊓ pointStabilizer v : Subgroup (Equiv.Perm Ω))).subtype
      Subtype.val_injective).trans (primeRank_mono 3 (by
        intro g hg
        exact ⟨hle hg.2,hg.1⟩))
end BinaryPermutation.SevenTriangle
