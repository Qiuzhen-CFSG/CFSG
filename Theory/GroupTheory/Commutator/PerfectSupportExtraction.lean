module
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.ThreeSubgroups
public import Mathlib.GroupTheory.IsPerfect

/-!
# Extracting a perfect actor's support from a conjugate span

Suppose K has at most two H-conjugates, K and C. A seed A lies in a
candidate support W, the relative normalizer of K preserves W, and C
centralizes A. Every H-conjugate of A then centralizes K modulo W.
If these conjugates exhaust [U,R] with K <= R, the second commutator
[[U,K],K] lies in W. Relative three-subgroups and perfectness recover
[U,K] <= W. No central quotient or covering kernel is discarded.

Source application: Aschbacher--Smith14.6.22, printed p.1038,
in Chapter14's ComponentSupports/Modules/Recognition/IndividualSupports.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

/-- Recover a perfect actor's full support from an exhausted conjugate span.
The other conjugacy type fixes the seed; the component normalizer preserves
its proposed support. All groups and central kernels remain in the original ambient group. -/
theorem commutator_eq_of_exhausted_pair_span
    (H U K C R A W : Subgroup G) [Group.IsPerfect K] [IsMulCommutative U]
    (hKH : K ≤ H) (hKR : K ≤ R) (hHU : H ≤ normalizer (U : Set G))
    (hAW : A ≤ W) (hWU : W ≤ U) (hWK : W ≤ ⁅U,K⁆)
    (hWN : H ⊓ normalizer (K : Set G) ≤ normalizer (W : Set G))
    (hAC : A ≤ centralizer (C : Set G))
    (hpair : ∀ h ∈ H, K.map (MulAut.conj h).toMonoidHom = K ∨
      K.map (MulAut.conj h).toMonoidHom = C)
    (hexhaust : ⁅U,R⁆ = conjugateSpanBy A H) : ⁅U,K⁆ = W := by
  have hKW : K ≤ normalizer (W : Set G) :=
    (le_inf hKH K.le_normalizer).trans hWN
  have hUW : U ≤ normalizer (W : Set G) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hWU)).trans (centralizer_le_normalizer _)
  let F := commutatorPreimage U K W
  have hWF : W ≤ F := le_commutatorPreimage hWU
    (le_normalizer_iff_commutator_le_left.mp hKW)
  have hspan : conjugateSpanBy A H ≤ F := by
    rw [conjugateSpanBy_eq_iSup_conj]
    apply iSup_le
    intro h
    by_cases hn : (h:G) ∈ normalizer (K : Set G)
    · exact (map_mono hAW).trans
        ((mem_normalizer_iff_map_conj_eq.mp (hWN ⟨h.property,hn⟩)).le.trans hWF)
    · have he : K.map (MulAut.conj (h:G)⁻¹).toMonoidHom = C :=
        (hpair (h:G)⁻¹ (H.inv_mem h.property)).resolve_left
          (fun hh => hn ((normalizer (K : Set G)).inv_mem_iff.mp
            (mem_normalizer_iff_map_conj_eq.mpr hh)))
      apply le_commutatorPreimage
      · exact (map_mono (hAW.trans hWU)).trans
          (mem_normalizer_iff_map_conj_eq.mp (hHU h.property)).le
      · apply (commutator_eq_bot_iff_le_centralizer.mpr ?_).le.trans bot_le
        rintro _ ⟨a,ha,rfl⟩
        apply mem_centralizer_iff.mpr
        intro k hk
        have hc := mem_centralizer_iff.mp (hAC ha) _
          (he ▸ mem_map_of_mem (MulAut.conj (h:G)⁻¹).toMonoidHom hk)
        have hh := congrArg (MulAut.conj (h:G)) hc
        simpa only [map_mul,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,
          mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,mul_inv_cancel,inv_mul_cancel,mul_one,one_mul] using hh
  have hd : ⁅⁅U,K⁆,K⁆ ≤ W :=
    (commutator_mono ((commutator_mono le_rfl hKR).trans
      (hexhaust.le.trans hspan)) le_rfl).trans
        (commutator_commutatorPreimage_le U K W hUW)
  have hr := commutator_commutator_le_of_rotate_of_le_normalizer hKW hKW hUW
    (by simpa only [commutator_comm K U] using hd) hd
  rw [K.commutator_eq_self,commutator_comm K U] at hr
  exact le_antisymm hr hWK
end Subgroup
