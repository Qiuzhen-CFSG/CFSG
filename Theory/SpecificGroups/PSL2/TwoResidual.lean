module

public import BenderSuzuki.Converse.PSL2
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.GroupTheory.IsPerfect

/-!
# The two-residual of binary PSL₂

For a field of order at least four, the usual transvection calculation makes
PSL₂ perfect, so its two-residual and derived subgroup are both the whole group.
At field order two, transport to S₃. Its cubic commutator generates the derived
subgroup and its quotient has exponent two, giving the same residual equality.
The small permutation identities are verified by kernel reduction.

This retains the derived endpoint X(2^(n/2))′ in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 16.1.4(4), printed p.1171.
-/

public section

namespace Theory.PSL2
open Subgroup
open scoped commutatorElement
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

private theorem perm_three_residual : pResidual 2 (Equiv.Perm (Fin 3)) = commutator (Equiv.Perm (Fin 3)) := by
  let r : Equiv.Perm (Fin 3) := ⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2⁆
  have hr : r ^ 3 = 1 := by decide +kernel
  have hrmem : r ∈ commutator (Equiv.Perm (Fin 3)) :=
    commutator_mem_commutator (mem_top _) (mem_top _)
  have hcases : ∀ a b : Equiv.Perm (Fin 3),
      ⁅a,b⁆ = 1 ∨ ⁅a,b⁆ = r ∨ ⁅a,b⁆ = r ^ 2 := by decide +kernel
  have hsquares : ∀ a : Equiv.Perm (Fin 3),
      a ^ 2 = 1 ∨ a ^ 2 = r ∨ a ^ 2 = r ^ 2 := by decide +kernel
  have hR : r ∈ pResidual 2 (Equiv.Perm (Fin 3)) :=
    mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hr))
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, ?_⟩
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator (Equiv.Perm (Fin 3))) q
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    rcases hsquares g with h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hrmem
    · rw [h]; exact pow_mem hrmem _
  · rw [commutator_def]
    apply commutator_le.mpr
    intro a _ b _
    rcases hcases a b with h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hR
    · rw [h]; exact pow_mem hR _

/-- The two-residual of binary PSL₂ is its derived subgroup, including
PSL₂(2), whose residual is a proper subgroup. -/
theorem binary_twoResidual_eq_commutator {n : ℕ} (hn : 0 < n) :
    pResidual 2 (PSL2BinaryMatrixGroup n) = commutator (PSL2BinaryMatrixGroup n) := by
  rcases Nat.eq_or_lt_of_le hn with h | h
  · have hn1 : n = 1 := h.symm
    subst n
    obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two
      (show Nat.card (BinaryGaloisField 1) = 2 by
        simpa [BinaryGaloisField] using GaloisField.card 2 1 (by norm_num))
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_pResidual, perm_three_residual]
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  · obtain ⟨x, hx, hx1⟩ := BenderSuzuki.Converse.exists_ne_zero_ne_one n h
    have hc : commutator (PSL2BinaryMatrixGroup n) = ⊤ :=
      SL2Simple.PSL_commutator_eq_top ⟨x, hx, fun hs => by
        rcases sq_eq_one_iff.mp hs with hs | hs
        · exact hx1 hs
        · exact hx1 (by simpa only [CharTwo.neg_eq] using hs)⟩
    let : Group.IsPerfect (PSL2BinaryMatrixGroup n) := ⟨hc⟩
    rw [hc]
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN hP
    let := hN
    have : Subsingleton (PSL2BinaryMatrixGroup n ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ hP.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

end Theory.PSL2
