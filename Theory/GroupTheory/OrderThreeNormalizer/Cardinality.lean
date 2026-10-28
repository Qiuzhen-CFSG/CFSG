module
public import Theory.GroupTheory.OrderThreeNormalizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cardinality of an order-three normalizer

The normalizer acts on the cyclic subgroup of order three, whose automorphism
group has order two. A specified inverter makes that action onto; its kernel
is precisely the centralizer. Thus the normalizer has twice the centralizer's
order. This supplies the literal finite normalizer count in F.1.12.
-/

public section
noncomputable section
namespace Subgroup


theorem normalizer_card_of_order_three_inverter {G:Type*} [Group G] [Finite G]
    (r f:G) (hr:orderOf r=3) (hf:f*r*f⁻¹=r⁻¹) :
    Nat.card (normalizer (zpowers r:Set G))=2*Nat.card (centralizer ({r}:Set G)) := by
  let P:=zpowers r
  have hi:r⁻¹≠r := by
    intro hi
    have h2:r^2=1 := by
      rw [pow_two]
      nth_rw 1 [←hi]
      exact inv_mul_cancel r
    have hd:=orderOf_dvd_of_pow_eq_one h2
    rw [hr] at hd
    norm_num at hd
  have hfN:f∈normalizer (P:Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (f*r*f⁻¹)=zpowers r
    rw [hf,zpowers_inv]
  have hAut:Nat.card (MulAut P)=2 := by
    rw [IsCyclic.card_mulAut,Nat.card_zpowers,hr]
    decide
  have hn:P.normalizerMonoidHom ⟨f,hfN⟩≠1 := by
    intro h
    have he:=congrArg (fun α:MulAut P=>(α ⟨r,mem_zpowers r⟩:G)) h
    change f*r*f⁻¹=r at he
    exact hi (hf.symm.trans he)
  have hne:P.normalizerMonoidHom.range≠⊥ := by
    intro h
    have hm: P.normalizerMonoidHom ⟨f,hfN⟩∈P.normalizerMonoidHom.range :=
      ⟨⟨f,hfN⟩,rfl⟩
    rw [h,mem_bot] at hm
    exact hn hm
  have hR:Nat.card P.normalizerMonoidHom.range=2 := by
    have hd:=P.normalizerMonoidHom.range.card_subgroup_dvd_card
    rw [hAut] at hd
    have hl:=P.normalizerMonoidHom.range.one_lt_card_iff_ne_bot.mpr hne
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with h|h
    · omega
    · exact h
  have hC:centralizer (P:Set G)=centralizer ({r}:Set G) := by
    rw [show P=closure ({r}:Set G) from zpowers_eq_closure r,centralizer_closure]
  have hK:Nat.card P.normalizerMonoidHom.ker=Nat.card (centralizer ({r}:Set G)) := by
    rw [normalizerMonoidHom_ker,Nat.card_congr
      (subgroupOfEquivOfLe (centralizer_le_normalizer (P:Set G))).toEquiv,hC]
  have h:=P.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker,hK,hR,mul_comm] at h
  exact h.symm


end Subgroup
