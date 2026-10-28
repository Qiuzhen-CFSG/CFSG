module

public import Theory.GroupTheory.QuaternionCentralProductC2Rank
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry.Basic
public import Theory.GroupTheory.QuaternionCentralProductFactors

/-!
# Suzuki type c₂ on the actual quaternion central quotient

The predicate below is Definition E.2.6 literally: the quotient automorphism
squares to one, its moved space has dimension two, and some vector is not
perpendicular to its image under the polar form of the intrinsic square form.
All spaces and actions are on the actual Q/Z(Q), using its given quaternion
factor embeddings. No fixed-subgroup order is assumed.

Rank–nullity first gives a fixed quotient of order four. An automorphism
interchanges or preserves the two quaternion factors. Interchange would make
all vectors perpendicular to their images, so c₂ preserves both factors.
If one restriction were inner, that factor's quotient plane would be the
whole fixed space. The displacement of the other plane is fixed and lies in
both planes, hence is zero; that would make the whole quotient fixed. Thus
both restrictions are outer, giving exactly the input consumed by the
index-two rank calculation. This argument only requires an involution on
the quotient, not an involutive lift.

Source: Aschbacher–Smith, Definition E.2.6, printed p.218, and Lemma
14.4.4(2),(6), printed pp.1007–1008, refs/quasithin.pdf.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

/-- Suzuki's c2 condition on the actual central quotient and its square form. -/
public structure IsC2 (a : MulAut Q) : Prop where
  involutive : (quotientAut (center Q) a)^2=1
  moved_dimension : Module.finrank (ZMod 2)
    (LinearMap.range ((d.quotientLinearAction a).toLinearMap - LinearMap.id)) = 2
  nonorthogonal : ∃ v : d.SquareSpace,
    d.quadraticForm.polarBilin v (d.quotientLinearAction a v) ≠ 0

private abbrev q (x : Q) : d.SquareSpace := Additive.ofMul (QuotientGroup.mk' (center Q) x)

private theorem polar_zero_iff (x y : Q) :
    d.quadraticForm.polarBilin (q d x) (q d y) = 0 ↔ Commute x y := by
  rw [d.polarBilin_mk, d.centerCoordinate_eq_zero_iff]
  constructor
  · intro h
    exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr h.eq)

private theorem linear_apply (a : MulAut Q) (v : d.SquareSpace) :
    d.quotientLinearAction a v = Additive.ofMul (quotientAut (center Q) a v.toMul) :=
  d.quotientLinearAction_apply a v.toMul

private theorem linear_apply_q (a : MulAut Q) (x : Q) :
    d.quotientLinearAction a (q d x) = q d (a x) := by
  rw [linear_apply]
  exact congrArg Additive.ofMul (quotientAut_apply_mk (center Q) a x)

private theorem polar_invariant (a : MulAut Q) (v w : d.SquareSpace) :
    d.quadraticForm.polarBilin (d.quotientLinearAction a v) (d.quotientLinearAction a w) =
      d.quadraticForm.polarBilin v w := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    ← map_add (d.quotientLinearAction a)]
  have hi (u : d.SquareSpace) : d.quadraticForm (d.quotientLinearAction a u) =
      d.quadraticForm u := by
        rw [linear_apply]
        exact d.quadraticForm_invariant a u.toMul
  rw [hi,hi,hi]

private theorem quotient_action_square (a : MulAut Q)
    (ha : (quotientAut (center Q) a)^2=1) (v : d.SquareSpace) :
    d.quotientLinearAction a (d.quotientLinearAction a v) = v := by
  rw [linear_apply, linear_apply]
  exact congrArg Additive.ofMul (show quotientAut (center Q) a
    (quotientAut (center Q) a v.toMul) = v.toMul from
      by simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun ha v.toMul)

private theorem swap_orthogonal (a : MulAut Q)
    (ha : (quotientAut (center Q) a)^2=1)
    (hL : d.left.map a.toMonoidHom = d.right)
    (hR : d.right.map a.toMonoidHom = d.left) :
    ∀ v : d.SquareSpace, d.quadraticForm.polarBilin v (d.quotientLinearAction a v) = 0 := by
  intro v
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (center Q) v.toMul
  have hv : v = q d x := congrArg Additive.ofMul hx.symm
  subst v
  have hn : d.left ≤ normalizer (d.right : Set Q) :=
    (show d.left ≤ centralizer (d.right : Set Q) from
      fun b hb c hc => (d.commute b hb c hc).symm).trans (centralizer_le_normalizer _)
  have hm : x ∈ (↑(d.left ⊔ d.right) : Set Q) := d.span ▸ mem_top x
  rw [coe_mul_of_left_le_normalizer_right _ _ hn] at hm
  obtain ⟨b,hb,c,hc,rfl⟩ := hm
  have hLb : a b ∈ d.right := hL.le (mem_map_of_mem a.toMonoidHom hb)
  have hRc : a c ∈ d.left := hR.le (mem_map_of_mem a.toMonoidHom hc)
  have hb0 : d.quadraticForm.polarBilin (q d b) (d.quotientLinearAction a (q d b)) = 0 := by
    rw [linear_apply_q]
    exact (polar_zero_iff d b (a b)).mpr (d.commute b hb (a b) hLb)
  have hc0 : d.quadraticForm.polarBilin (q d c) (d.quotientLinearAction a (q d c)) = 0 := by
    rw [linear_apply_q]
    exact (polar_zero_iff d c (a c)).mpr (d.commute (a c) hRc c hc).symm
  have he : d.quadraticForm.polarBilin (q d b) (d.quotientLinearAction a (q d c)) =
      d.quadraticForm.polarBilin (q d c) (d.quotientLinearAction a (q d b)) := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply]
    have hh := polar_invariant d a (q d c) (d.quotientLinearAction a (q d b))
    rw [quotient_action_square d a ha] at hh
    exact hh
  change d.quadraticForm.polarBilin (q d b + q d c)
    (d.quotientLinearAction a (q d b + q d c)) = 0
  simp only [map_add, LinearMap.add_apply, hb0, hc0, zero_add, add_zero, he]
  exact CharTwo.add_self_eq_zero _

omit [Finite Q] in
private theorem factor_card (B : Subgroup Q) (hB : Nonempty (B ≃* QuaternionGroup 2)) :
    Nat.card B = 8 := by
  obtain ⟨e⟩ := hB
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

include d in
private theorem factor_image_card (B : Subgroup Q) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hz : center Q ≤ B) : Nat.card (B.map (QuotientGroup.mk' (center Q))) = 4 := by
  have hBindex : B.index = 4 := by
    have h := B.card_mul_index
    rw [factor_card B hB,d.card] at h
    omega
  have hi := B.index_map_eq (QuotientGroup.mk'_surjective (center Q))
    (show (QuotientGroup.mk' (center Q)).ker ≤ B by rwa [QuotientGroup.ker_mk'])
  have hh := (B.map (QuotientGroup.mk' (center Q))).card_mul_index
  rw [hi,hBindex,d.quotient_card] at hh
  omega

/-- Rank–nullity derives the order of the fixed quotient from the source moved dimension. -/
public theorem IsC2.fixed_quotient_card {a : MulAut Q} (h : d.IsC2 a) :
    Nat.card ((quotientAut (center Q) a).toMonoidHom.eqLocus
      (MonoidHom.id (Q ⧸ center Q))) = 4 := by
  let f := (d.quotientLinearAction a).toLinearMap - LinearMap.id
  have hk : Module.finrank (ZMod 2) (LinearMap.ker f) = 2 := by
    have hh := LinearMap.finrank_range_add_finrank_ker f
    rw [h.moved_dimension,d.quotient_finrank] at hh
    omega
  let e : ((quotientAut (center Q) a).toMonoidHom.eqLocus
      (MonoidHom.id (Q ⧸ center Q))) ≃ LinearMap.ker f := {
    toFun := fun x => ⟨Additive.ofMul x.val, by
      change d.quotientLinearAction a (Additive.ofMul x.val) - Additive.ofMul x.val = 0
      rw [linear_apply]
      exact sub_eq_zero.mpr (congrArg Additive.ofMul x.property)⟩
    invFun := fun x => ⟨x.val.toMul, by
      have hx : d.quotientLinearAction a x.val - x.val = 0 := x.property
      rw [linear_apply] at hx
      exact congrArg Additive.toMul (sub_eq_zero.mp hx)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), hk, Nat.card_zmod]
  rfl

private theorem factor_images_disjoint :
    d.left.map (QuotientGroup.mk' (center Q)) ⊓
      d.right.map (QuotientGroup.mk' (center Q)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro v ⟨⟨b,hb,hbv⟩,⟨c,hc,hcv⟩⟩
  have hbc : b⁻¹*c ∈ center Q := QuotientGroup.eq.mp (hbv.trans hcv.symm)
  have hcB : c ∈ d.left := by
    have h := d.left.mul_mem hb ((d.center_eq ▸ hbc).1)
    simpa only [mul_inv_cancel_left] using h
  have hcZ : c ∈ center Q := d.center_eq.symm ▸ ⟨hcB,hc⟩
  rw [mem_bot,← hcv]
  exact (QuotientGroup.eq_one_iff _).mpr hcZ

private theorem not_inner_of_fixed_four (a : MulAut Q)
    (ha : (quotientAut (center Q) a)^2=1)
    (hF : Nat.card ((quotientAut (center Q) a).toMonoidHom.eqLocus
      (MonoidHom.id (Q ⧸ center Q))) = 4)
    (hR : d.right.map a.toMonoidHom = d.right) :
    ¬ ∃ b : d.left, ∀ x : d.left, a (x : Q) = (b : Q)*x*(b : Q)⁻¹ := by
  let _ := d.quotient_elementary
  let π := QuotientGroup.mk' (center Q)
  let t := quotientAut (center Q) a
  let F := t.toMonoidHom.eqLocus (MonoidHom.id (Q ⧸ center Q))
  have hinv (v : Q ⧸ center Q) : v⁻¹=v := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      d.quotient_elementary.exponent_dvd_p v
  have ht2 (v : Q ⧸ center Q) : t (t v)=v := by
    simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using DFunLike.congr_fun ha v
  rintro ⟨b,hb⟩
  have hLF : d.left.map π ≤ F := by
    rintro v ⟨x,hx,rfl⟩
    change t (π x) = π x
    rw [quotientAut_apply_mk,hb ⟨x,hx⟩]
    change π ((b : Q)*x*(b : Q)⁻¹) = π x
    rw [map_mul,map_mul,map_inv,mul_comm (π (b : Q)),mul_inv_cancel_right]
  have hLF_eq : d.left.map π = F := eq_of_le_of_card_ge hLF (by
    rw [hF,factor_image_card d d.left d.left_model (d.center_eq ▸ inf_le_left)])
  have hRF : d.right.map π ≤ F := by
    rintro v ⟨c,hc,rfl⟩
    have hdiffF : (π c)⁻¹*t (π c) ∈ F := by
      change t ((π c)⁻¹*t (π c)) = (π c)⁻¹*t (π c)
      rw [map_mul,map_inv,ht2,hinv,hinv,mul_comm]
    have hdiffR : (π c)⁻¹*t (π c) ∈ d.right.map π := by
      have he : t (π c) = π (a c) := quotientAut_apply_mk (center Q) a c
      rw [he]
      rw [← map_inv,← map_mul]
      exact mem_map_of_mem π (d.right.mul_mem (d.right.inv_mem hc)
        (hR.le (mem_map_of_mem a.toMonoidHom hc)))
    have hdiff1 : (π c)⁻¹*t (π c) = 1 := by
      apply mem_bot.mp
      rw [← factor_images_disjoint d]
      exact ⟨hLF_eq.symm ▸ hdiffF,hdiffR⟩
    exact (inv_mul_eq_one.mp hdiff1).symm
  have htop : F = ⊤ := by
    apply top_unique
    have h := sup_le hLF hRF
    rwa [← map_sup,d.span,map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at h
  have hh : Nat.card F = 16 := by
    rw [htop,Nat.card_congr (topEquiv : (⊤ : Subgroup (Q ⧸ center Q)) ≃* _).toEquiv]
    exact d.quotient_card
  have hh' : (16 : ℕ) = 4 := hh.symm.trans hF
  omega

/-- The precise source c2 condition forces preservation and outer restriction on both factors. -/
public theorem IsC2.bothOuter {a : MulAut Q} (h : d.IsC2 a) : d.BothOuter a := by
  have images (B : Subgroup Q) (hB : Nonempty (B ≃* QuaternionGroup 2)) :
      B.map a.toMonoidHom = d.left ∨ B.map a.toMonoidHom = d.right := by
    obtain ⟨e⟩ := hB
    exact quaternion_subgroup_eq_factor d.left d.right _ d.left_model d.right_model
      d.intersection_card d.commute ⟨(a.subgroupMap B).symm.trans e⟩ (by rw [d.span]; exact le_top)
  have hLR : d.left ≠ d.right := by
    intro he
    have hi := d.intersection_card
    rw [he,inf_idem,factor_card d.right d.right_model] at hi
    omega
  have hm : d.left.map a.toMonoidHom = d.left ∧ d.right.map a.toMonoidHom = d.right := by
    rcases images d.left d.left_model with hL | hL
    · refine ⟨hL,?_⟩
      rcases images d.right d.right_model with hR | hR
      · exact (hLR (map_injective a.injective (hL.trans hR.symm))).elim
      · exact hR
    · have hR : d.right.map a.toMonoidHom = d.left := by
        rcases images d.right d.right_model with hR | hR
        · exact hR
        · exact (hLR (map_injective a.injective (hL.trans hR.symm))).elim
      obtain ⟨v,hv⟩ := h.nonorthogonal
      exact (hv (swap_orthogonal d a h.involutive hL hR v)).elim
  refine ⟨hm.1,hm.2,not_inner_of_fixed_four d a h.involutive
    (IsC2.fixed_quotient_card d h) hm.2,?_⟩
  let d' : QuaternionCentralProductData Q := {
    left := d.right, right := d.left, left_model := d.right_model, right_model := d.left_model,
    intersection_card := by rw [inf_comm]; exact d.intersection_card,
    commute := fun c hc b hb => (d.commute b hb c hc).symm,
    span := by rw [sup_comm]; exact d.span }
  exact not_inner_of_fixed_four d' a h.involutive (IsC2.fixed_quotient_card d h) hm.1

end Subgroup.QuaternionCentralProductData
