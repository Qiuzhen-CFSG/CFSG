module

public import Theory.GroupTheory.QuaternionCentralProductAutomorphisms
public import Theory.GroupTheory.CentralProductEquivalence
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel

/-!
# Lifting quaternion factor automorphisms and counting the quotient action

For two embedded commuting quaternion eights generating a finite group with
intersection of order two, every pair of factor automorphisms extends to the
whole group. Factor equivalences preserve the common central involution;
the central-product gluing theorem therefore descends their direct-product
map through the actual overlap. The same construction interchanges the factors.

The factor stabilizer contains 24 * 24 distinct lifts, and interchange makes
its index at least two. Together with the existing upper bound this proves
that the full automorphism group has order 1152. Its action on the actual
central quotient has the inner group of order 16 as kernel, hence image order 72.

This supplies the order calculation for the identification of the outer action
with O₄⁺(2) used in Aschbacher–Smith, Lemma 14.2.21, printed p.988, PDF p.1005
of `refs/quasithin.pdf`. The orthogonal identification itself is a separate step.
-/

namespace Subgroup.QuaternionCentralProductData

open scoped Pointwise

variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

private theorem left_center : (center d.left).map d.left.subtype = center Q := by
  rw [← intersection_eq_factor_center d.left d.right d.left_model d.intersection_card
    d.commute, d.center_eq]

private theorem right_center : (center d.right).map d.right.subtype = center Q := by
  rw [← intersection_eq_factor_center d.right d.left d.right_model
    (by simpa [inf_comm] using d.intersection_card)
    (fun c hc b hb => (d.commute b hb c hc).symm), inf_comm, d.center_eq]

include d in
private theorem factor_equiv_fixes_center (B C : Subgroup Q)
    (hB : (center B).map B.subtype = center Q)
    (hC : (center C).map C.subtype = center Q)
    (e : B ≃* C) (z : B) (hz : (z : Q) ∈ center Q) : (e z : Q) = z := by
  have hzB : z ∈ center B := by
    rw [← hB] at hz
    obtain ⟨w, hw, he⟩ := hz
    have he' : w = z := Subtype.ext he
    exact he' ▸ hw
  have hez : (e z : Q) ∈ center Q := by
    rw [← hC]
    exact ⟨e z, (centerCongr e ⟨z, hzB⟩).property, rfl⟩
  by_cases hz1 : z = 1
  · simp [hz1]
  · have hn : (⟨z, hz⟩ : center Q) ≠ 1 := by
      intro h
      exact hz1 (Subtype.ext (congrArg (fun z : center Q => (z : Q)) h))
    have hen : (⟨e z, hez⟩ : center Q) ≠ 1 := by
      intro h
      have he : e z = 1 := Subtype.ext (congrArg (fun z : center Q => (z : Q)) h)
      exact hz1 (e.injective (he.trans e.map_one.symm))
    obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp d.center_card
    exact congrArg Subtype.val ((hw ⟨e z, hez⟩ hen).trans (hw ⟨z, hz⟩ hn).symm)

/-- Equivalences of the embedded factors extend to the whole central product. -/
public theorem exists_factor_extension (d' : QuaternionCentralProductData Q)
    (a : d.left ≃* d'.left) (b : d.right ≃* d'.right) :
    ∃ e : MulAut Q, (∀ x : d.left, e x = (a x : Q)) ∧
      ∀ y : d.right, e y = (b y : Q) := by
  apply exists_mulEquiv_of_central_products d.left d.right d'.left d'.right
    (fun x y => d.commute x x.property y y.property)
    (fun x y => d'.commute x x.property y y.property) d.span d'.span a b
  have forward (D E : QuaternionCentralProductData Q)
      (f : D.left ≃* E.left) (g : D.right ≃* E.right)
      (x : D.left) (y : D.right) (hxy : (x : Q) = y) : (f x : Q) = g y := by
    have hx : (x : Q) ∈ center Q := by
      rw [D.center_eq]
      exact ⟨x.property, hxy ▸ y.property⟩
    have hy : (y : Q) ∈ center Q := hxy ▸ hx
    rw [factor_equiv_fixes_center D _ _ D.left_center E.left_center f x hx,
      factor_equiv_fixes_center D _ _ D.right_center E.right_center g y hy, hxy]
  intro x y
  constructor
  · exact forward d d' a b x y
  · intro h
    simpa using forward d' d a.symm b.symm (a x) (b y) h

/-- Every pair of factor automorphisms descends to an automorphism of the central product. -/
public theorem exists_factor_lift (a : MulAut d.left) (b : MulAut d.right) :
    ∃ e : MulAut Q, (∀ x : d.left, e x = (a x : Q)) ∧
      ∀ y : d.right, e y = (b y : Q) :=
  d.exists_factor_extension d a b

omit [Finite Q] in
private theorem map_eq_of_restriction (B C : Subgroup Q) (e : MulAut Q)
    (a : B ≃* C) (he : ∀ x : B, e x = (a x : Q)) : B.map e.toMonoidHom = C := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [show e.toMonoidHom x = (a ⟨x, hx⟩ : Q) from he ⟨x, hx⟩]
    exact (a ⟨x, hx⟩).property
  · intro hy
    refine ⟨a.symm ⟨y, hy⟩, (a.symm ⟨y, hy⟩).property, ?_⟩
    exact (he _).trans (congrArg Subtype.val (a.apply_symm_apply _))

/-- An automorphism interchanges the two actual embedded quaternion factors. -/
public theorem exists_factor_swap : ∃ e : MulAut Q,
    d.left.map e.toMonoidHom = d.right ∧ d.right.map e.toMonoidHom = d.left := by
  let d' : QuaternionCentralProductData Q :=
    { left := d.right
      right := d.left
      left_model := d.right_model
      right_model := d.left_model
      intersection_card := by simpa [inf_comm] using d.intersection_card
      commute := fun c hc b hb => (d.commute b hb c hc).symm
      span := by simpa [sup_comm] using d.span }
  obtain ⟨l⟩ := d.left_model
  obtain ⟨r⟩ := d.right_model
  let a := l.trans r.symm
  obtain ⟨e, heL, heR⟩ := d.exists_factor_extension d' a a.symm
  exact ⟨e, map_eq_of_restriction d.left d.right e a heL,
    map_eq_of_restriction d.right d.left e a.symm heR⟩

include d in
/-- The full automorphism group has order 1152. -/
public theorem card_mulAut : Nat.card (MulAut Q) = 1152 := by
  classical
  let H := MulAction.stabilizer (MulAut Q) d.left
  let lift (p : MulAut d.left × MulAut d.right) : MulAut Q :=
    (d.exists_factor_lift p.1 p.2).choose
  have hl (p : MulAut d.left × MulAut d.right) :=
    (d.exists_factor_lift p.1 p.2).choose_spec
  let f : MulAut d.left × MulAut d.right → H := fun p =>
    ⟨lift p, map_eq_of_restriction d.left d.left (lift p) p.1 (hl p).1⟩
  have hf : Function.Injective f := by
    intro p q h
    have he : lift p = lift q := congrArg Subtype.val h
    apply Prod.ext
    · apply MulEquiv.ext
      intro x
      apply Subtype.ext
      exact ((hl p).1 x).symm.trans ((DFunLike.congr_fun he (x : Q)).trans ((hl q).1 x))
    · apply MulEquiv.ext
      intro x
      apply Subtype.ext
      exact ((hl p).2 x).symm.trans ((DFunLike.congr_fun he (x : Q)).trans ((hl q).2 x))
  have hH : 576 ≤ Nat.card H := by
    have h := Nat.card_le_card_of_injective f hf
    obtain ⟨l⟩ := d.left_model
    obtain ⟨r⟩ := d.right_model
    simpa only [Nat.card_prod, Nat.card_congr (MulAut.congr l).toEquiv,
      Nat.card_congr (MulAut.congr r).toEquiv, QuaternionGroup.card_mulAut_two] using h
  have hne : d.left ≠ d.right := by
    intro h
    obtain ⟨l⟩ := d.left_model
    have hc : Nat.card d.left = 8 := by
      rw [Nat.card_congr l.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hi := d.intersection_card
    rw [← h, inf_idem, hc] at hi
    omega
  have hindex : 2 ≤ H.index := by
    apply H.one_lt_index_of_ne_top
    intro ht
    obtain ⟨e, he, _⟩ := d.exists_factor_swap
    have hm : e ∈ H := ht ▸ mem_top e
    have hfix : d.left.map e.toMonoidHom = d.left := hm
    exact hne (hfix.symm.trans he)
  have hlo := Nat.mul_le_mul hH hindex
  rw [H.card_mul_index] at hlo
  have hhi := Nat.le_of_dvd (by decide : 0 < 1152)
    (card_mulAut_dvd_of_quaternion_central_product d.left d.right d.left_model
      d.right_model d.intersection_card d.commute d.span)
  omega

include d in
/-- The kernel of the action on the central quotient has order sixteen. -/
public theorem quotientAut_ker_card : Nat.card (quotientAut (center Q)).ker = 16 := by
  rw [d.quotientAut_ker_eq_inner]
  have hc : (MulAut.conj : Q →* MulAut Q).ker = center Q := by
    ext x
    constructor
    · intro hx
      apply mem_center_iff.mpr
      intro y
      have he : MulAut.conj x = 1 := hx
      have hxy : x * y * x⁻¹ = y := DFunLike.congr_fun he y
      exact ((mul_inv_eq_iff_eq_mul).mp hxy).symm
    · intro hx
      change MulAut.conj x = 1
      ext y
      change x * y * x⁻¹ = y
      rw [← mem_center_iff.mp hx y, mul_inv_cancel_right]
  have h := (MulAut.conj : Q →* MulAut Q).ker.card_mul_index
  rw [index_ker, hc, d.center_card, d.card] at h
  omega

include d in
/-- The image of the actual action on the central quotient has order 72. -/
public theorem quotientAut_range_card : Nat.card (quotientAut (center Q)).range = 72 := by
  have h := (quotientAut (center Q)).ker.card_mul_index
  rw [index_ker, d.quotientAut_ker_card, d.card_mulAut] at h
  omega

end Subgroup.QuaternionCentralProductData
