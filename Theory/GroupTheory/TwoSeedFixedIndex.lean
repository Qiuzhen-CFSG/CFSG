module
public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.GroupTheory.Index

/-!
# A quotient bound from two conjugate fixed-subgroup indices

Let A act on an abelian section Q/(Q ∩ N), with no nonzero fixed coset.
If E and one A-conjugate generate A modulo Q, and E fixes a subgroup of
index at most d, the section has order at most d². The conjugate has the
same fixed-index bound. Their common fixed preimage centralizes both
actors and Q modulo N, so is contained in N. The intersection-index
inequality gives the bound.

All normality is relative to A. In particular N need not be contained in Q
or normal in the ambient group. SuzukiSecondKernelUpper applies this to
the literal radius-two kernel in DGS85 (12.6), printed p.183.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Two conjugate seed bounds control the entire fixed-point-free section. -/
theorem index_le_sq_of_two_conjugate_seeds (A Q E N : Subgroup G) [Finite Q]
    (hQA : Q ≤ A) (hEA : E ≤ A)
    (hAQ : A ≤ normalizer (Q : Set G)) (hAN : A ≤ normalizer (N : Set G))
    (hQQ : ⁅Q,Q⁆ ≤ N)
    (hfixed : commutatorPreimage Q A N = Q ⊓ N)
    (g : G) (hg : g ∈ A)
    (hgen : (E ⊔ E.map (MulAut.conj g).toMonoidHom) ⊔ Q = A)
    {d : ℕ} (hindex : (commutatorPreimage Q E N).relIndex Q ≤ d) :
    N.relIndex Q ≤ d^2 := by
  let f := (MulAut.conj g).toMonoidHom
  let E' := E.map f
  let C := commutatorPreimage Q E N
  let C' := commutatorPreimage Q E' N
  let I := C ⊓ C'
  have hQ : Q.map f = Q := mem_normalizer_iff_map_conj_eq.mp (hAQ hg)
  have hN : N.map f = N := mem_normalizer_iff_map_conj_eq.mp (hAN hg)
  have hQN := hQA.trans hAN
  have hC : C.map f ≤ C' := by
    apply le_commutatorPreimage
    · exact (map_mono (commutatorPreimage_le _ _ _)).trans_eq hQ
    · have hh := map_mono (f := f) (commutator_commutatorPreimage_le Q E N hQN)
      rw [map_commutator,hN] at hh
      exact hh
  have hi' : C'.relIndex Q ≤ d := by
    have hh := relIndex_le_of_le_left hC
      (show ((C.map f).subgroupOf Q).index ≠ 0 from index_ne_zero_of_finite)
    have hm : (C.map f).relIndex Q = C.relIndex Q := by
      calc
        _ = (C.map f).relIndex (Q.map f) := congrArg _ hQ.symm
        _ = _ := relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
    exact (hh.trans_eq hm).trans hindex
  have hIQ : I ≤ Q := inf_le_left.trans (commutatorPreimage_le _ _ _)
  have hI : I ≤ N := by
    have hAE : A ≤ commutatorPreimage A I N := by
      conv_lhs => rw [←hgen]
      apply sup_le
      · apply sup_le
        · apply le_commutatorPreimage hEA
          rw [commutator_comm]
          exact (commutator_mono inf_le_left le_rfl).trans
            (commutator_commutatorPreimage_le Q E N hQN)
        · apply le_commutatorPreimage
          · exact (map_mono hEA).trans_eq (mem_normalizer_iff_map_conj_eq.mp (A.le_normalizer hg))
          · rw [commutator_comm]
            exact (commutator_mono inf_le_right le_rfl).trans
              (commutator_commutatorPreimage_le Q E' N hQN)
      · exact le_commutatorPreimage hQA ((commutator_mono le_rfl hIQ).trans hQQ)
    have hc : ⁅I,A⁆ ≤ N := by
      rw [commutator_comm]
      exact (commutator_mono hAE le_rfl).trans
        (commutator_commutatorPreimage_le A I N hAN)
    exact (le_commutatorPreimage hIQ hc).trans (hfixed.le.trans inf_le_right)
  have hupper : I.relIndex Q ≤ d^2 :=
    (relIndex_inf_le (H := C) (K := C') (L := Q)).trans
      (by simpa only [pow_two] using Nat.mul_le_mul hindex hi')
  exact (relIndex_le_of_le_left hI
    (show (I.subgroupOf Q).index ≠ 0 from index_ne_zero_of_finite)).trans hupper


end Subgroup

