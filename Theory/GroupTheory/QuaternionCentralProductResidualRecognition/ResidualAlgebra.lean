module
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.OrthogonalWreath
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Mathlib.GroupTheory.IndexNormal
/-!
# Canonical full orthogonal action and its original residual

A self-centralizing quaternion central product of order 32 in an order-2304
extension has the full binary orthogonal outer action. Its recognized residual
has two commuting SL2(3) factors, order 288 and odd quotient of order nine.
Joining it to the original order-128 two-subgroup gives a normal subgroup
whose intersection with the ambient two-subgroup is exactly the original one.

Source: Aschbacher--Smith 2.4.29, printed p.546. These are the actual residual
and transfer-subgroup premises, with the canonical conjugation action retained.
-/
@[expose] public section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {G : Type*} [Group G] [Finite G]
variable (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)

noncomputable def normalWreathAction : G →* BinaryFourPlus.Wreath :=
  d.quotientWreathAction.comp MulAut.conjNormal

theorem normalWreathAction_ker (hcent : centralizer (Q : Set G) ≤ Q) :
    (d.normalWreathAction Q).ker = Q := by
  apply le_antisymm
  · intro g hg
    have ha : (MulAut.conjNormal g : MulAut Q) ∈ MulAut.innerSubgroup Q := by
      rw [← d.quotientWreathAction_ker]
      exact hg
    obtain ⟨q,hq⟩ := ha
    have hk : (MulAut.conjNormal (q.val⁻¹*g) : MulAut Q)=1 := by
      have he : (MulAut.conjNormal q.val : MulAut Q)=MulAut.conj q := by
        ext x
        rfl
      rw [map_mul,map_inv,he,hq,inv_mul_cancel]
    have hc : q.val⁻¹*g ∈ centralizer (Q : Set G) := by
      intro x hx
      have hh := congrArg (fun b : MulAut Q => (b ⟨x,hx⟩ : G)) hk
      change (q.val⁻¹*g)*x*(q.val⁻¹*g)⁻¹=x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    simpa only [mul_inv_cancel_left] using Q.mul_mem q.property (hcent hc)
  · intro g hg
    change MulAut.conjNormal g ∈ d.quotientWreathAction.ker
    rw [d.quotientWreathAction_ker]
    exact ⟨⟨g,hg⟩,by ext x; rfl⟩

theorem normalWreathAction_surjective (hcent : centralizer (Q : Set G) ≤ Q)
    (hc : Nat.card G = 2304) : Function.Surjective (d.normalWreathAction Q) := by
  have hw : Nat.card BinaryFourPlus.Wreath = 72 :=
    (Nat.card_congr BinaryFourPlus.isometryEquivWreath.toEquiv).symm.trans
      BinaryFourPlus.card_isometrySubgroup
  apply MonoidHom.surjective_of_card_ker_le_div
  rw [d.normalWreathAction_ker Q hcent,d.card,hc,hw]

variable (r : QuaternionResidualCentralProduct Q d)
include d r

omit [Finite G] [Q.Normal] in
theorem residual_contains_core : Q ≤ pResidual 2 G := by
  have hh : (d.left.map Q.subtype) ⊔ (d.right.map Q.subtype)=Q := by
    rw [← map_sup,d.span,← MonoidHom.range_eq_map,range_subtype]
  rw [←hh]
  exact sup_le (r.left_contains.trans (r.span ▸ le_sup_left))
    (r.right_contains.trans (r.span ▸ le_sup_right))

omit [Q.Normal] in
theorem residual_card : Nat.card (pResidual 2 G) = 288 := by
  obtain ⟨el⟩ := r.left_model
  obtain ⟨er⟩ := r.right_model
  have hl : Nat.card r.left=24 := (Nat.card_congr el.toEquiv).trans
    GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have hr : Nat.card r.right=24 := (Nat.card_congr er.toEquiv).trans
    GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have hi : Nat.card (r.left ⊓ r.right : Subgroup G)=2 := by
    rw [r.intersection,card_map_of_injective Q.subtype_injective,d.center_card]
  have hn : r.right ≤ normalizer (r.left : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro a ha b hb
    exact r.commute b hb a ha
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes r.left r.right hn
  rw [hl,hr,hi,r.span] at hc
  omega

theorem residual_image_card :
    Nat.card ((pResidual 2 G).map (QuotientGroup.mk' Q)) = 9 := by
  let I := pResidual 2 G
  let f := (QuotientGroup.mk' Q).comp I.subtype
  have hk : f.ker=Q.subgroupOf I := by
    ext x
    exact QuotientGroup.eq_one_iff x.val
  have hf : f.range=I.map (QuotientGroup.mk' Q) := by
    rw [MonoidHom.range_comp,range_subtype]
  have hh := f.ker.card_mul_index
  rw [index_ker,hf,hk,Nat.card_congr (subgroupOfEquivOfLe (d.residual_contains_core Q r)).toEquiv,
    d.card,d.residual_card Q r] at hh
  dsimp only [I] at hh
  omega

theorem residual_inf_two_subgroup_le (A : Subgroup G) (hA : IsPGroup 2 A) :
    pResidual 2 G ⊓ A ≤ Q := by
  let f := QuotientGroup.mk' Q
  have h3 : IsPGroup 3 ((pResidual 2 G).map f) :=
    IsPGroup.of_card (n:=2) (by rw [d.residual_image_card Q r]; norm_num)
  have hd : Disjoint (A.map f) ((pResidual 2 G).map f) :=
    (hA.map f).disjoint_of_coprime h3 (by decide)
  intro x hx
  have hm : f x ∈ A.map f ⊓ (pResidual 2 G).map f :=
    ⟨mem_map_of_mem f hx.2,mem_map_of_mem f hx.1⟩
  exact (QuotientGroup.eq_one_iff x).mp (hd.le_bot hm)

omit [Q.Normal] in
theorem residual_wreath_card (f : G →* BinaryFourPlus.Wreath)
    (hf : Function.Surjective f) (hk : f.ker=Q) :
    Nat.card (pResidual 2 BinaryFourPlus.Wreath)=9 := by
  let I := pResidual 2 G
  let g := f.comp I.subtype
  have hgk : g.ker=Q.subgroupOf I := by
    ext x
    change f x=1 ↔ (x:G)∈Q
    change (x:G)∈f.ker ↔ (x:G)∈Q
    rw [hk]
  have hgr : g.range=pResidual 2 BinaryFourPlus.Wreath := by
    rw [MonoidHom.range_comp,range_subtype]
    exact map_pResidual_of_surjective 2 f hf
  have hh := g.ker.card_mul_index
  rw [index_ker,hgr,hgk,
    Nat.card_congr (subgroupOfEquivOfLe (d.residual_contains_core Q r)).toEquiv,
    d.card,d.residual_card Q r] at hh
  omega

theorem residual_join_normal (S : Subgroup G) (hS : IsPGroup 2 S)
    (hQS : Q≤S) (hcS : Nat.card S=128) (hcG : Nat.card G=2304) :
    (pResidual 2 G ⊔ S).Normal := by
  have hi : pResidual 2 G ⊓ S=Q := le_antisymm
    (d.residual_inf_two_subgroup_le Q r S hS)
    (le_inf (d.residual_contains_core Q r) hQS)
  have hn : S≤normalizer (pResidual 2 G : Set G) := by
    rw [(pResidual 2 G).normalizer_eq_top]
    exact le_top
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (pResidual 2 G) S hn
  rw [d.residual_card Q r,hcS,hi,d.card] at hh
  have hc : Nat.card (pResidual 2 G ⊔ S : Subgroup G)=1152 := by omega
  have hh' := (pResidual 2 G ⊔ S).card_mul_index
  rw [hc,hcG] at hh'
  apply normal_of_index_eq_two
  omega

theorem residual_join_inf_two_subgroup (S T : Subgroup G)
    (hT : IsPGroup 2 T) (hQS : Q≤S) (hST : S≤T) :
    (pResidual 2 G ⊔ S) ⊓ T=S := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i,hi,s,hs,hx'⟩ := mem_sup_of_normal_left.mp hx.1
    have hit : i∈T := by
      have hh := T.mul_mem hx.2 (T.inv_mem (hST hs))
      simpa only [←hx',mul_inv_cancel_right] using hh
    have hiq := d.residual_inf_two_subgroup_le Q r T hT ⟨hi,hit⟩
    rw [←hx']
    exact S.mul_mem (hQS hiq) hs
  · exact le_inf le_sup_right hST

end Subgroup.QuaternionCentralProductData
