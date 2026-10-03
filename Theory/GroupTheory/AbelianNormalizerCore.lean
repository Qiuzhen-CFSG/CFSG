module
public import Theory.PGroupCore

/-!
# An abelian subgroup recovered from its normalizer core

Let W be an abelian p-subgroup of a finite group whose p-core is
self-centralizing. If the p-core of the normalizer of W, mapped into the
ambient group, is contained in W, then W is the whole ambient p-core.
No solvability or ambient normality assumption on W is required.

Write R for the ambient p-core. Its intersection with the normalizer of
W is a normal p-subgroup of that normalizer, hence lies in W. In the
p-group W∨R, the normal-right product decomposition then makes W
self-normalizing. The nilpotent normalizer condition gives R≤W.
Abelianness makes W centralize R, and the self-centralizing core gives
the reverse inclusion.

Source: the normalizer-condition argument immediately before assertion
(10) in Stellmacher (10.1)(a3), Journal of Algebra 190 (1997), printed p.62.
This generic result isolates the passage from a local normalizer core to
the full core, retaining the literal normalizer and subtype map.
-/

namespace Subgroup

public theorem eq_pCore_of_abelian_normalizer_core_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (W : Subgroup G) [IsMulCommutative W] (hW : IsPGroup p W)
    (hchar : centralizer (pCore p G : Set G) ≤ pCore p G)
    (hnorm : (pCore p (normalizer (W:Set G))).map
      (normalizer (W:Set G)).subtype ≤ W) : W=pCore p G := by
  let R := pCore p G
  let N := normalizer (W:Set G)
  have hRN : R ⊓ N ≤ W := by
    intro r hr
    have hcore : R.subgroupOf N ≤ pCore p N :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    exact hnorm (mem_map_of_mem N.subtype (hcore (show (⟨r,hr.2⟩:N) ∈ R.subgroupOf N from hr.1)))
  let J := W ⊔ R
  have hJ : IsPGroup p J := hW.to_sup_of_normal_right pCore_isPGroup
  let _ : Group.IsNilpotent J := hJ.isNilpotent
  have hself : normalizer (W.subgroupOf J : Set J)=W.subgroupOf J := by
    apply le_antisymm ?_ le_normalizer
    intro x hx
    have hxN : (x:G) ∈ N := by
      rw [← subgroupOf_normalizer_eq (show W≤J from le_sup_left)] at hx
      exact hx
    obtain ⟨w,hw,r,hr,hwr⟩ := mem_sup_of_normal_right.mp x.property
    have hwrN : w*r ∈ N := hwr.symm ▸ hxN
    have hrN : r ∈ N := by
      simpa only [← mul_assoc,inv_mul_cancel,one_mul] using
        N.mul_mem (N.inv_mem (W.le_normalizer hw)) hwrN
    change (x:G) ∈ W
    exact hwr ▸ W.mul_mem hw (hRN ⟨hr,hrN⟩)
  have htop : W.subgroupOf J=⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G:=J))) _ hself
  have hRW : R ≤ W := le_sup_right.trans (subgroupOf_eq_top.mp htop)
  apply le_antisymm ?_ hRW
  apply le_trans ?_ hchar
  intro w hw
  rw [mem_centralizer_iff]
  intro r hr
  exact setLike_mul_comm (s:=W) (hRW hr) hw

end Subgroup

