module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.QuaternionCentralProductOuterInvolution
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.GroupTheory.IndexNormal

/-!
# Rank of an index-two extension of a quaternion central product

An elementary subgroup of Q₈ * Q₈ intersects a quaternion factor in at most
its two square-one elements. The product formula gives order at most eight.
In an index-two extension whose outside action preserves both factors and
is outer on each, every outside elementary subgroup intersects the core in
a subgroup of the fixed four of one of its outside involutions. Thus it too
has order at most eight. An embedded elementary eight supplies rank three.

The outside representative is arbitrary: inner twists preserve both outer
restrictions. Only the involution selected from an elementary subgroup is
required to square to one. The source c2-to-factor passage is supplied in
QuaternionCentralProductC2Action, using the intrinsic square form.

Source: Aschbacher–Smith, Lemma 14.4.4(6), printed pp.1007–1008.
The inner-twist proof follows the factor decomposition used in
QuaternionCentralProductSquareAction.
-/

open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

/-- Preservation of both embedded quaternion factors, with outer restriction on each. -/
public structure BothOuter (a : MulAut Q) : Prop where
  left_map : d.left.map a.toMonoidHom = d.left
  right_map : d.right.map a.toMonoidHom = d.right
  left_outer : ¬ ∃ b : d.left, ∀ x : d.left, a (x : Q) = (b : Q) * x * (b : Q)⁻¹
  right_outer : ¬ ∃ b : d.right, ∀ x : d.right, a (x : Q) = (b : Q) * x * (b : Q)⁻¹

omit [Finite Q] in
private theorem factor_normalizes (B C : Subgroup Q)
    (hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) (hs : B ⊔ C = ⊤) :
    (⊤ : Subgroup Q) ≤ normalizer (B : Set Q) := by
  rw [← hs]
  exact sup_le B.le_normalizer ((show C ≤ centralizer (B : Set Q) from fun c hc' b hb => hc b hb c hc').trans
    (centralizer_le_normalizer _))

omit [Finite Q] in
private theorem conj_factor_inner (B C : Subgroup Q)
    (hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) (hs : B ⊔ C = ⊤) (q : Q) :
    ∃ b : B, ∀ x : B, (MulAut.conj q) (x : Q) = (b : Q) * x * (b : Q)⁻¹ := by
  have hn : B ≤ normalizer (C : Set Q) := by
    exact (show B ≤ centralizer (C : Set Q) from fun b hb c hc' => (hc b hb c hc').symm).trans
      (centralizer_le_normalizer _)
  have hq : q ∈ (↑(B ⊔ C) : Set Q) := hs ▸ mem_top q
  rw [coe_mul_of_left_le_normalizer_right B C hn] at hq
  obtain ⟨b, hb, c, hc', rfl⟩ := hq
  refine ⟨⟨b,hb⟩, fun x => ?_⟩
  have hx : (MulAut.conj c) (x : Q) = x := by
    change c * (x : Q) * c⁻¹ = x
    rw [← hc x x.property c hc', mul_inv_cancel_right]
  rw [map_mul, MulAut.mul_apply, hx, MulAut.conj_apply]

omit [Finite Q] in
private theorem outer_twist (B C : Subgroup Q)
    (hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) (hs : B ⊔ C = ⊤)
    (a : MulAut Q) (hm : B.map a.toMonoidHom = B) (q : Q)
    (ho : ¬ ∃ b : B, ∀ x : B, a (x : Q) = (b : Q)*x*(b : Q)⁻¹) :
    ¬ ∃ b : B, ∀ x : B, (MulAut.conj q * a) (x : Q) = (b : Q)*x*(b : Q)⁻¹ := by
  obtain ⟨c,hc'⟩ := conj_factor_inner B C hc hs q
  rintro ⟨b,hb⟩
  apply ho
  refine ⟨c⁻¹*b, fun x => ?_⟩
  have hx : a (x : Q) ∈ B := hm.le (mem_map_of_mem a.toMonoidHom x.property)
  have hh := hb x
  change (MulAut.conj q) (a (x : Q)) = _ at hh
  rw [hc' ⟨a (x : Q),hx⟩] at hh
  apply (MulAut.conj (c : Q)).injective
  change (c : Q) * a (x : Q) * (c : Q)⁻¹ = _
  rw [hh]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  group

omit [Finite Q] in
public theorem BothOuter.inner_twist {a : MulAut Q} (h : d.BothOuter a) (q : Q) :
    d.BothOuter (MulAut.conj q * a) := by
  have hcl := mem_normalizer_iff_map_conj_eq.mp
    (factor_normalizes d.left d.right d.commute d.span (mem_top q))
  have hcr := mem_normalizer_iff_map_conj_eq.mp
    (factor_normalizes d.right d.left (fun c hc b hb => (d.commute b hb c hc).symm)
      (by rw [sup_comm]; exact d.span) (mem_top q))
  refine ⟨?_, ?_, outer_twist _ _ d.commute d.span a h.left_map q h.left_outer,
    outer_twist _ _ (fun c hc b hb => (d.commute b hb c hc).symm)
      (by rw [sup_comm]; exact d.span) a h.right_map q h.right_outer⟩
  · change d.left.map ((MulAut.conj q).toMonoidHom.comp a.toMonoidHom) = d.left
    rw [← map_map, h.left_map]
    exact hcl
  · change d.right.map ((MulAut.conj q).toMonoidHom.comp a.toMonoidHom) = d.right
    rw [← map_map, h.right_map]
    exact hcr

include d in
public theorem elementary_card_le_eight (E : Subgroup Q) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ 8 := by
  obtain ⟨e⟩ := d.left_model
  have hB : Nat.card d.left = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hi : Nat.card (d.left ⊓ E : Subgroup Q) ≤ 2 := by
    let R := {x : QuaternionGroup 2 // x^2=1}
    have hR : Nat.card R = 2 := by rw [Nat.card_eq_fintype_card]; decide
    let f : (d.left ⊓ E : Subgroup Q) → R := fun x => ⟨e ⟨x,x.property.1⟩, by
      rw [← map_pow]
      have hx : (⟨x,x.property.1⟩ : d.left)^2=1 := by
        let _ := hE
        exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : Q) x.property.2)
      rw [hx,map_one]⟩
    have hf : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : d.left => (z : Q)) (e.injective (congrArg Subtype.val hxy)))
    exact hR ▸ Nat.card_le_card_of_injective f hf
  have hn : E ≤ normalizer (d.left : Set Q) :=
    le_top.trans (factor_normalizes d.left d.right d.commute d.span)
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes d.left E hn
  have hbound : Nat.card (d.left ⊔ E : Subgroup Q) ≤ 32 :=
    d.card ▸ (d.left ⊔ E).card_le_card_group
  rw [hB] at hh
  nlinarith

public theorem BothOuter.fixed_card {a : MulAut Q} (h : d.BothOuter a) (ha : a^2=1) :
    Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id Q)) = 4 :=
  (quaternion_central_product_outer_involution d.left d.right d.left_model d.right_model
    d.span d.intersection_card d.commute a ha h.left_map h.right_map h.left_outer
    h.right_outer).2.1
end Subgroup.QuaternionCentralProductData

namespace Subgroup
variable {P : Type*} [Group P] [Finite P] (U : Subgroup P) [U.Normal]
    (d : QuaternionCentralProductData U)

omit [Finite P] in
private theorem conjNormal_mem (u : U) :
    (MulAut.conjNormal (u : P) : MulAut U) = MulAut.conj u := by
  ext x
  rfl

omit [Finite P] in
/-- All representatives of the nontrivial coset have outer restrictions on both factors. -/
public theorem quaternion_bothOuter_of_outside
    (hi : U.index = 2) (a : P) (ha : a ∉ U)
    (hc2 : d.BothOuter (MulAut.conjNormal a)) (x : P) (hx : x ∉ U) :
    d.BothOuter (MulAut.conjNormal x) := by
  have hq : x * a⁻¹ ∈ U := (U.mul_mem_iff_of_index_two hi).mpr (by
    simp only [inv_mem_iff, hx, ha])
  let q : U := ⟨x*a⁻¹,hq⟩
  have he : (MulAut.conjNormal x : MulAut U) = MulAut.conj q * MulAut.conjNormal a := by
    rw [← conjNormal_mem, ← map_mul]
    simp only [q, inv_mul_cancel_right]
  rw [he]
  exact QuaternionCentralProductData.BothOuter.inner_twist d hc2 q

/-- The intersection formula and the fixed four bound every elementary subgroup. -/
public theorem quaternion_index_two_elementary_card_le
    (hi : U.index = 2) (a : P) (ha : a ∉ U)
    (hc2 : d.BothOuter (MulAut.conjNormal a))
    (E : Subgroup P) (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 8 := by
  let _ := hE
  by_cases hEU : E ≤ U
  · have h := d.elementary_card_le_eight (E.subgroupOf U) (IsElementaryAbelian.subgroupOf hEU)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hEU).toEquiv] at h
  · obtain ⟨x,hxE,hxU⟩ := SetLike.not_le_iff_exists.mp hEU
    let α : MulAut U := MulAut.conjNormal x
    have hx2 : x^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hxE
    have hα : α^2=1 := by
      dsimp [α]
      rw [← map_pow, hx2, map_one]
    have hc : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id U)) = 4 :=
      QuaternionCentralProductData.BothOuter.fixed_card d
        (quaternion_bothOuter_of_outside U d hi a ha hc2 x hxU) hα
    have hle : E.subgroupOf U ≤ α.toMonoidHom.eqLocus (MonoidHom.id U) := by
      intro y hy
      change α y = y
      apply Subtype.ext
      change x * (y : P) * x⁻¹ = y
      have hcomm : x * (y : P) = (y : P) * x :=
        congrArg Subtype.val ((hE.toIsMulCommutative).is_comm.comm
          (⟨x,hxE⟩ : E) ⟨y,hy⟩)
      rw [hcomm,mul_inv_cancel_right]
    have hsmall : Nat.card (E.subgroupOf U) ≤ 4 := hc ▸ card_le_of_le hle
    have hcard : Nat.card (U.subgroupOf E) = Nat.card (E.subgroupOf U) := by
      let e : U.subgroupOf E ≃ E.subgroupOf U := {
        toFun := fun y => ⟨⟨y,y.property⟩,y.val.property⟩
        invFun := fun y => ⟨⟨y,y.property⟩,y.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      exact Nat.card_congr e
    have hind : (U.subgroupOf E).index = 2 := by
      have hd := U.relIndex_dvd_index_of_normal E
      rw [hi] at hd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
      · exact (hEU (relIndex_eq_one.mp h)).elim
      · exact h
    have hh := (U.subgroupOf E).card_mul_index
    rw [hind,hcard] at hh
    omega

/-- An index-two extension with the indicated outside action has order 64 and rank three. -/
public theorem quaternion_index_two_rank
    (hi : U.index = 2) (a : P) (ha : a ∉ U)
    (hc2 : d.BothOuter (MulAut.conjNormal a))
    (V : Subgroup U) (hV : IsElementaryAbelian 2 V) (hVcard : Nat.card V = 8) :
    Nat.card P = 64 ∧ primeRank 2 P = 3 := by
  have hc : Nat.card P = 64 := by
    have hh := U.card_mul_index
    rw [d.card,hi] at hh
    omega
  refine ⟨hc, le_antisymm ?_ ?_⟩
  · exact (primeRank_le_iff_elementary_card_le P).mpr
      (quaternion_index_two_elementary_card_le U d hi a ha hc2)
  · let _ := hV
    let _ : CommGroup V := IsMulCommutative.instCommGroup
    exact primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hV.exponent_dvd_p)
      hVcard (U.subtype.comp V.subtype) (U.subtype_injective.comp V.subtype_injective)
end Subgroup
