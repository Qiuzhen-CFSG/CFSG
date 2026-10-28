module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OuterInvolutions.Certificate
/-!
# Fusion of all outer involutions in the actual Aut(M₁₂) carrier

An outer element multiplied by the fixed outer seed lies in the index-two
inner subgroup. Its literal block restriction therefore gives the marker
used by the checked eight-word Sylow certificate. Sylow conjugacy then proves
fusion for every outer involution of the verified degree-24 carrier.
Source: Aschbacher–Smith H.11.1 and K.4.2.
-/
public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OuterInvolutions
open Subgroup OverlapExtensions
theorem seed_not_mem_inner : seed ∉ inner := by
  intro hi
  have h := blockRestriction_spec ⟨seed, hi⟩ 0
  have hn : ∀ i : Fin 12, generatorA (blockLabel 0) ≠ blockLabel i := by decide +kernel
  exact hn ((blockRestriction ⟨seed, hi⟩).val 0) h

private theorem outer_product (x : Carrier) (ho : x ∉ inner) : seed * x ∈ inner := by
  exact (Subgroup.mul_mem_iff_of_index_two (H := inner) (a := seed) (b := x)
    inner_index).mpr (iff_of_false seed_not_mem_inner ho)

private theorem outer_marker (x : Carrier) (ho : x ∉ inner) :
    ∃ j : Fin 12, generatorA (x.val (blockLabel 0)) = blockLabel j := by
  let y : inner := ⟨seed * x, outer_product x ho⟩
  refine ⟨(blockRestriction y).val 0, ?_⟩
  have hb := blockRestriction_spec y 0
  have hval : y.val.val = generatorA * x.val := rfl
  rw [hval, Equiv.Perm.mul_apply] at hb
  exact hb

theorem sylow_fusion (x : overlap) (hx : orderOf (x : Carrier) = 2)
    (ho : (x : Carrier) ∉ inner) : IsConj seed (x : Carrier) := by
  have hp : (x : Carrier) ^ 2 = 1 := by
    simpa only [hx] using pow_orderOf_eq_one (x : Carrier)
  have hb := outer_marker x ho
  obtain ⟨i, hi⟩ := Overlap.element_surjective x
  rw [← hi] at hp hb ⊢
  exact sylow_fusion_of_marker i hp hb

theorem fusion (x : Carrier) (hx : orderOf x = 2) (ho : x ∉ inner) : IsConj seed x := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier P VerifiedPair.commonSylow
  have hmem : MulAut.conj g x ∈ overlap := by
    have he := (P.equivSMul g ⟨x, hP (mem_zpowers x)⟩).property
    change MulAut.conj g x ∈ (g • P : Sylow 2 Carrier) at he
    rw [hg] at he
    exact he
  have hi : inner.Normal := Subgroup.normal_of_index_eq_two inner_index
  have hout : MulAut.conj g x ∉ inner := by
    intro ht
    apply ho
    have hh := hi.conj_mem (MulAut.conj g x) ht g⁻¹
    simpa only [MulAut.conj_apply, inv_mul_cancel_left, mul_inv_rev, inv_inv, mul_assoc,
      mul_inv_cancel, inv_mul_cancel, mul_one] using hh
  have hh := sylow_fusion ⟨_, hmem⟩ ((MulAut.conj g).orderOf_eq x |>.trans hx) hout
  exact hh.trans (isConj_iff.mpr ⟨g, rfl⟩).symm
end Sporadic.Mathieu.M12ExceptionalExtension.OuterInvolutions
