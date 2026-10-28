module
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.ResidualUpper
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfection of the first two binary parabolic residuals

The residuals at nodes zero and one generate every elementary root with
row in the first three coordinates. For each such root there is a third
coordinate in that block, expressing the root as a commutator of two
roots in the same group. The cubic and incident-root descriptions of the
literal residuals then prove that their join is perfect.

The proof uses the actual partial-flag stabilizers and their embedded
O²-residuals in arbitrary binary dimension at least three. It supplies
the model calculation for K = ⟨Y₀,Y₂⟩ in Aschbacher--Smith 15.1.29,
printed pp.1103--1104 of `refs/quasithin.pdf`.
-/

public section
open Subgroup
open scoped commutatorElement
namespace BinaryLinear.OrderedResidualConjugators
open OuterCyclic InvariantNodeActions

private theorem head_root_commutator {m : ℕ} (b : Basis m) (r k s : Fin (m + 1))
    (hrk : r ≠ k) (hrs : r ≠ s) (hks : k ≠ s) :
    ⁅root b r k hrk, root b k s hks⁆ = root b r s hrs := by
  have h : CubicPairNormalizers.CoreAbsorption.root r k hrk 1 *
      CubicPairNormalizers.CoreAbsorption.root k s hks 1 *
      CubicPairNormalizers.CoreAbsorption.root r k hrk 1 =
      CubicPairNormalizers.CoreAbsorption.root r s hrs 1 *
      CubicPairNormalizers.CoreAbsorption.root k s hks 1 := by
    ext v j
    simp only [LinearEquiv.mul_apply, CubicPairNormalizers.CoreAbsorption.root_apply, mul_one]
    by_cases hjr : j = r <;> by_cases hjk : j = k <;>
      simp [hjr, hjk, hrk, hrk.symm, hrs.symm, hks.symm] <;> ring_nf <;>
      simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero]
  have hh : root b r k hrk * root b k s hks * root b r k hrk =
      root b r s hrs * root b k s hks := by
    simpa only [map_mul,root] using congrArg (MulAut.conj b.equivFun.symm) h
  rw [commutatorElement_def,root_inv,root_inv,hh]
  have hsquare : root b k s hks * root b k s hks = 1 := by
    nth_rw 1 [← root_inv b k s hks]
    exact inv_mul_cancel _
  rw [mul_assoc,hsquare,mul_one]

private theorem head_root_mem {m : ℕ} (hm : 2 ≤ m) (b : Basis m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) (hr : r.val < 3) :
    root b r s hrs ∈
      nodeResidual b ⟨0,by omega⟩ ⊔ nodeResidual b ⟨1,by omega⟩ := by
  let K := nodeResidual b ⟨0,by omega⟩ ⊔ nodeResidual b ⟨1,by omega⟩
  let z : Fin (m + 1) := ⟨0,by omega⟩
  let o : Fin (m + 1) := ⟨1,by omega⟩
  let w : Fin (m + 1) := ⟨2,by omega⟩
  have h01 : root b z o (by simp [z,o]) ∈ K := mem_sup_right
    (incident_root_mem_nodeResidual b ⟨1,by omega⟩ _ _ _
      (Or.inl ⟨by simp [z],Or.inl rfl⟩))
  have h12 : root b o w (by simp [o,w]) ∈ K := mem_sup_left
    (incident_root_mem_nodeResidual b ⟨0,by omega⟩ _ _ _
      (Or.inr ⟨Or.inr rfl,by simp [w]⟩))
  have h10 : root b o z (by simp [o,z]) ∈ K := by
    have hc : cubic b z o (by simp [z,o]) ∈ K :=
      mem_sup_left (cubic_mem_nodeResidual b ⟨0,by omega⟩)
    have hh := K.mul_mem (K.inv_mem h01) hc
    simpa only [cubic, inv_mul_cancel_left] using hh
  have h21 : root b w o (by simp [w,o]) ∈ K := by
    have hc : cubic b o w (by simp [o,w]) ∈ K :=
      mem_sup_right (cubic_mem_nodeResidual b ⟨1,by omega⟩)
    have hh := K.mul_mem (K.inv_mem h12) hc
    simpa only [cubic, inv_mul_cancel_left] using hh
  have h20 : root b w z (by simp [w,z]) ∈ K := by
    rw [←head_root_commutator b w o z (by simp [w,o]) (by simp [w,z]) (by simp [o,z])]
    exact le_normalizer_iff_commutator_le_left.mp K.le_normalizer (commutator_mem_commutator h21 h10)
  by_cases hs : 2 < s.val
  · rcases (show r = z ∨ r = o ∨ r = w from by
      rcases (show r.val = 0 ∨ r.val = 1 ∨ r.val = 2 by omega) with hh | hh | hh
      · exact Or.inl (Fin.ext hh)
      · exact Or.inr (Or.inl (Fin.ext hh))
      · exact Or.inr (Or.inr (Fin.ext hh))) with he | he | he
    · simp only [he]
      exact mem_sup_left (incident_root_mem_nodeResidual b ⟨0,by omega⟩ _ _ _
        (Or.inr ⟨Or.inl rfl,by change 1 < s.val; omega⟩))
    · simp only [he]
      exact mem_sup_left (incident_root_mem_nodeResidual b ⟨0,by omega⟩ _ _ _
        (Or.inr ⟨Or.inr rfl,by change 1 < s.val; omega⟩))
    · simp only [he]
      exact mem_sup_right (incident_root_mem_nodeResidual b ⟨1,by omega⟩ _ _ _
        (Or.inr ⟨Or.inr rfl,hs⟩))
  · have hne : r.val ≠ s.val := fun hh => hrs (Fin.ext hh)
    have hcases : (r = z ∧ s = o) ∨ (r = z ∧ s = w) ∨
        (r = o ∧ s = z) ∨ (r = o ∧ s = w) ∨
        (r = w ∧ s = z) ∨ (r = w ∧ s = o) := by
      have hc : (r.val = 0 ∧ s.val = 1) ∨ (r.val = 0 ∧ s.val = 2) ∨
        (r.val = 1 ∧ s.val = 0) ∨ (r.val = 1 ∧ s.val = 2) ∨
        (r.val = 2 ∧ s.val = 0) ∨ (r.val = 2 ∧ s.val = 1) := by omega
      simpa only [Fin.ext_iff,z,o,w] using hc
    rcases hcases with he | he | he | he | he | he <;> simp only [he.1,he.2]
    · exact h01
    · exact mem_sup_left (incident_root_mem_nodeResidual b ⟨0,by omega⟩ _ _ _
        (Or.inr ⟨Or.inl rfl,by simp [w]⟩))
    · exact h10
    · exact h12
    · exact h20
    · exact h21

/-- The actual join of the first two binary node residuals is perfect. -/
theorem first_two_residuals_perfect {m : ℕ} (hm : 2 ≤ m) (b : Basis m) :
    Group.IsPerfect (nodeResidual b ⟨0,by omega⟩ ⊔
      nodeResidual b ⟨1,by omega⟩ : Subgroup (LinearGroup (m + 1))) := by
  let K := nodeResidual b ⟨0,by omega⟩ ⊔ nodeResidual b ⟨1,by omega⟩
  have hr (r s : Fin (m + 1)) (hrs : r ≠ s) (hr : r.val < 3) :
      root b r s hrs ∈ ⁅K,K⁆ := by
    obtain ⟨k,hk,hkr,hks⟩ : ∃ k : Fin (m + 1), k.val < 3 ∧ k ≠ r ∧ k ≠ s := by
      have hfind : ∃ k : ℕ, k < 3 ∧ k ≠ r.val ∧ k ≠ s.val := by
        by_contra! hn
        have h0 := hn 0 (by decide)
        have h1 := hn 1 (by decide)
        have h2 := hn 2 (by decide)
        omega
      obtain ⟨k,hk,hkr,hks⟩ := hfind
      exact ⟨⟨k,by omega⟩,hk,fun he => hkr (congrArg Fin.val he),
        fun he => hks (congrArg Fin.val he)⟩
    rw [← head_root_commutator b r k s hkr.symm hrs hks]
    exact commutator_mem_commutator (head_root_mem hm b r k hkr.symm hr)
      (head_root_mem hm b k s hks hk)
  have hnode (i : Fin m) (hi : i.val < 2) : nodeResidual b i ≤ ⁅K,K⁆ := by
    rw [nodeResidual_eq_rootNode]
    apply (closure_le _).mpr
    rintro g (hg | ⟨r,s,hrs,hinc,rfl⟩)
    · rw [Set.mem_singleton_iff] at hg
      rw [hg,cubic]
      exact (⁅K,K⁆).mul_mem
        (hr _ _ _ (by simp only [Fin.val_castSucc]; omega))
        (hr _ _ _ (by simp only [Fin.val_succ]; omega))
    · apply hr r s hrs
      rcases hinc with ⟨hh,_⟩ | ⟨hh | hh,_⟩
      · omega
      · rw [hh]
        simp only [Fin.val_castSucc]
        omega
      · rw [hh]
        simp only [Fin.val_succ]
        omega
  apply isPerfect_iff.mpr
  exact le_antisymm (le_normalizer_iff_commutator_le_left.mp K.le_normalizer)
    (sup_le (hnode _ (by simp)) (hnode _ (by simp)))
end BinaryLinear.OrderedResidualConjugators
