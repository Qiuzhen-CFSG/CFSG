module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Cyclic displacement modulo a subgroup intersection

Let an element a with a²=1 normalize an abelian subgroup U, and let the Q-action
on U have its commutators in Z contained in both U and D. If all displacement
from the join of a and U lies in U, its image modulo U intersect D has
order bounded by the index in Q of a supplied subgroup R. It suffices that
the Q intersect R elements have their a-displacement in D.

The map q ↦ [q,a] modulo U intersect D is a homomorphism: conjugation by
Q is trivial on this quotient. Its kernel contains Q intersect R. Every
generator of the full joined displacement lies in this homomorphism's
image, because a has order at most two and U is abelian. The range-index
formula therefore proves the relative-index bound.

This source-neutral algebra is extracted from the source (9.4)(3) proof,
Stellmacher, printed p.51, for reuse with both O₂(O²(F)) and O₂(E_next).
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative
set_option maxHeartbeats 800000

private theorem cyclic_two_cases {G : Type*} [Group G] (a : G) (ha : a ^ 2 = 1)
    (x : G) (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  let K : Subgroup G := {
    carrier := {x | x = 1 ∨ x = a}
    one_mem' := Or.inl rfl
    mul_mem' := by
      rintro x y (rfl | rfl) (rfl | rfl) <;> simp_all [pow_two]
    inv_mem' := by
      rintro x (rfl | rfl)
      · simp
      · right
        exact inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ha) }
  exact (Subgroup.zpowers_le.mpr (show a ∈ K from Or.inr rfl)) hx

public theorem cyclic_displacement_relIndex_le
    {G : Type*} [Group G] [Finite G]
    (U Z D Q R : Subgroup G) [IsMulCommutative U]
    (a : G) (ha : a ^ 2 = 1)
    (haU : a ∈ Subgroup.normalizer (U : Set G))
    (hZU : Z ≤ U) (hZD : Z ≤ D)
    (hQ : ⁅U,Q⁆ ≤ Z)
    (hcomm : ⁅Subgroup.zpowers a ⊔ U,Q⁆ ≤ U)
    (hR : ∀ q ∈ Q ⊓ R, ⁅q,a⁆ ∈ D) :
    let W := ⁅Subgroup.zpowers a ⊔ U,Q⁆ ⊔ Z
    (U ⊓ D).relIndex W ≤ R.relIndex Q := by
  let C := Subgroup.zpowers a ⊔ U
  let W := ⁅C,Q⁆ ⊔ Z
  let J := U ⊓ D
  let JU := J.subgroupOf U
  let _ : JU.Normal := inferInstance
  let π := QuotientGroup.mk' JU
  have hc (q : Q) : ⁅(q:G),a⁆ ∈ U := by
    rw [Subgroup.commutator_comm] at hcomm
    exact hcomm (Subgroup.commutator_mem_commutator q.property
      ((le_sup_left : Subgroup.zpowers a ≤ C) (Subgroup.mem_zpowers a)))
  let value (q : Q) : U := ⟨⁅(q:G),a⁆, hc q⟩
  have hQU : Q ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hQ.trans hZU)
  have hfix (q : Q) (v : U) :
      π ⟨(q:G)*(v:G)*(q:G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hQU q.property) v).mp v.property⟩ = π v := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hh : ⁅(q:G),(v:G)⁆ ∈ Z := by
      rw [Subgroup.commutator_comm] at hQ
      exact hQ (Subgroup.commutator_mem_commutator q.property v.property)
    change (q:G)*(v:G)*(q:G)⁻¹ / (v:G) ∈ J
    simpa only [div_eq_mul_inv, commutatorElement_def] using (show ⁅(q:G),(v:G)⁆ ∈ J from ⟨hZU hh,hZD hh⟩)
  let f : Q →* (U ⧸ JU) := {
    toFun := fun q => π (value q)
    map_one' := by
      change π ⟨⁅(1:G),a⁆,_⟩ = 1
      rw [show (⟨⁅(1:G),a⁆,by simpa only [commutatorElement_one_left] using U.one_mem⟩ : U) = 1 from
        Subtype.ext (commutatorElement_one_left a)]
      exact π.map_one
    map_mul' := by
      intro q r
      have hval : value (q*r) =
          (⟨(q:G)*(value r:G)*(q:G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hQU q.property) (value r)).mp (value r).property⟩ : U) *
          value q := by
        apply Subtype.ext
        exact commutatorElement_mul_left_eq_conj_mul (q:G) (r:G) a
      rw [hval,map_mul,hfix,mul_comm] }
  have hker : R.subgroupOf Q ≤ f.ker := by
    intro q hq
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨hc q,hR q ⟨q.property,hq⟩⟩
  have hcard : Nat.card f.range ≤ R.relIndex Q := by
    rw [← Subgroup.index_ker]
    exact Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.index_dvd_of_le hker)
  have hWU : W ≤ U := sup_le hcomm hZU
  have hrange : (W.subgroupOf U).map π ≤ f.range := by
    rw [Subgroup.map_le_iff_le_comap]
    intro w hw
    change π w ∈ f.range
    have hw' : (w:G) ∈ ⁅C,Q⁆ ⊔ Z := hw
    let K := (f.range.comap π).map U.subtype
    have hWK : W ≤ K := by
      refine sup_le ?_ ?_
      · apply Subgroup.commutator_le.mpr
        intro c hcC q hq
        have haNorm : Subgroup.zpowers a ≤ Subgroup.normalizer (U : Set G) :=
          Subgroup.zpowers_le.mpr haU
        change c ∈ Subgroup.zpowers a ⊔ U at hcC
        rw [sup_comm] at hcC
        change c ∈ (↑(U ⊔ Subgroup.zpowers a) : Set G) at hcC
        rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ haNorm] at hcC
        obtain ⟨u,hu,b,hb,rfl⟩ := hcC
        rcases cyclic_two_cases a ha b hb with hb1 | hba
        · subst b
          simp only [mul_one]
          have hz : ⁅u,q⁆ ∈ Z := hQ (Subgroup.commutator_mem_commutator hu hq)
          refine ⟨⟨⁅u,q⁆,hZU hz⟩,?_,rfl⟩
          change π _ ∈ f.range
          have hz0 : π ⟨⁅u,q⁆,hZU hz⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨hZU hz,hZD hz⟩
          rw [hz0]
          exact f.range.one_mem
        · rw [hba]
          have hz : ⁅u,q⁆ ∈ Z := hQ (Subgroup.commutator_mem_commutator hu hq)
          have haqU : ⁅a,q⁆ ∈ U := hcomm (Subgroup.commutator_mem_commutator
            ((le_sup_left : Subgroup.zpowers a ≤ C) (Subgroup.mem_zpowers a)) hq)
          have heq : ⁅u*a,q⁆ = ⁅a,q⁆ * ⁅u,q⁆ := by
            rw [commutatorElement_mul_left_eq_conj_mul]
            have hucomm := setLike_mul_comm (s:=U) hu haqU
            rw [hucomm,mul_inv_cancel_right]
          refine ⟨⟨⁅u*a,q⁆,by rw [heq]; exact U.mul_mem haqU (hZU hz)⟩,?_,rfl⟩
          change π _ ∈ f.range
          have hinv : π ⟨⁅a,q⁆,haqU⟩ = (f ⟨q,hq⟩)⁻¹ := by
            change π ⟨⁅a,q⁆,haqU⟩ = (π (value ⟨q,hq⟩))⁻¹
            rw [← map_inv π]
            apply congrArg π
            apply Subtype.ext
            simp only [value, Subgroup.coe_inv]
            exact (commutatorElement_inv q a).symm
          have hmult : (⟨⁅u*a,q⁆,by rw [heq]; exact U.mul_mem haqU (hZU hz)⟩ : U) =
              ⟨⁅a,q⁆,haqU⟩ * ⟨⁅u,q⁆,hZU hz⟩ := Subtype.ext heq
          rw [hmult,map_mul,hinv,
            show π ⟨⁅u,q⁆,hZU hz⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨hZU hz,hZD hz⟩,
            mul_one]
          exact f.range.inv_mem (show f ⟨q,hq⟩ ∈ f.range from ⟨⟨q,hq⟩,rfl⟩)
      · intro z hz
        refine ⟨⟨z,hZU hz⟩,?_,rfl⟩
        change π _ ∈ f.range
        rw [show π ⟨z,hZU hz⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨hZU hz,hZD hz⟩]
        exact f.range.one_mem
    obtain ⟨w',hw',heq⟩ := hWK hw'
    have heqw : w' = w := Subtype.ext heq
    rw [heqw] at hw'
    exact hw'
  have hbound := (Subgroup.card_le_of_le hrange).trans hcard
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hWU] at hbound
  exact hbound

end Subgroup
