module
public import Theory.Representation.BinaryParabolicExteriorSquare.ComplementCore
public import Theory.GroupTheory.PResidual.NormalSubgroup.SimpleQuotient
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.FiniteLocalPair
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Recognizing the complementary-plane residual

The pointwise stabilizer of a binary plane has a two-perfect subgroup of
order forty-eight: the upper-right radical extended by the cubic on the
complement. Commutators with that cubic generate the radical. Every
nontrivial normal two-perfect subgroup of this residual is therefore the
whole residual. Six binary two-by-two blocks give the converse containment
for every two-perfect subgroup fixing the marked plane.

Source application: the actual L₀ matrix image in Aschbacher--Smith,
The Classification of Quasithin Groups, 13.8.31, printed p.965, with the
central-residual convention of Notation 13.2.1, printed p.877.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryParabolicExteriorSquare.PlaneRadical
open PlaneSpan

private theorem complement_displacement (v : Four) :
    Matrix.mulVec complementRadicalCubic (Matrix.mulVec complementRadicalCubic v) -
      Matrix.mulVec complementRadicalCubic v = v := by
  exact (by decide : ∀ v : Four,
    Matrix.mulVec complementRadicalCubic (Matrix.mulVec complementRadicalCubic v) -
      Matrix.mulVec complementRadicalCubic v = v) v

/-- The complement cubic generates the whole radical by commutators. -/
theorem radical_le_of_complement_mem (M : Subgroup SL)
    (hn : radical ≤ normalizer (M : Set SL)) (hc : complementElement ∈ M) :
    radical ≤ M := by
  rintro x ⟨v,hv⟩
  change element v.toAdd = x at hv
  subst x
  let w := Matrix.mulVec complementRadicalCubic v.toAdd
  have hw : element w ∈ radical := ⟨Multiplicative.ofAdd w,rfl⟩
  have hh : complementElement * (element w * complementElement⁻¹ * (element w)⁻¹) ∈ M :=
    M.mul_mem hc ((mem_normalizer_iff.mp (hn hw) _).mp (M.inv_mem hc))
  have hi : (element w)⁻¹ = element (-w) := by
    apply inv_eq_of_mul_eq_one_right
    rw [←element_add,add_neg_cancel,element_zero]
  rw [←mul_assoc,←mul_assoc,complement_radical_conjugation complementElement rfl,hi,
    ←element_add] at hh
  simpa only [←sub_eq_add_neg, w, complement_displacement] using hh

/-- The order-forty-eight complement group is two-perfect. -/
theorem complementLocal_twoPerfect : IsPPerfect 2 complementLocal := by
  let R := (pResidual 2 complementLocal).map complementLocal.subtype
  have hRn : radical ≤ normalizer (R : Set SL) :=
    (show radical ≤ complementLocal from le_sup_left).trans
      (le_normalizer_embedded_pResidual 2 complementLocal)
  have hc : complementElement ∈ R := by
    have hcL : complementElement ∈ complementLocal :=
      (show zpowers complementElement ≤ complementLocal from le_sup_right) (mem_zpowers _)
    refine ⟨⟨complementElement,hcL⟩,?_,rfl⟩
    apply mem_pResidual_of_orderOf_coprime
    rw [←complementLocal.orderOf_coe ⟨complementElement,hcL⟩,complementElement_order]
    decide
  have he : R = complementLocal := le_antisymm (map_subtype_le _)
    (sup_le (radical_le_of_complement_mem R hRn hc) (zpowers_le.mpr hc))
  apply (pResidual_eq_top_iff 2 complementLocal).mp
  apply map_injective complementLocal.subtype_injective
  simpa only [←MonoidHom.range_eq_map,range_subtype] using he

/-- A nontrivial normal two-perfect subgroup of the complement group is the whole group. -/
theorem eq_complementLocal_of_normal_twoPerfect (M : Subgroup SL)
    (hM : M ≤ complementLocal) (hn : complementLocal ≤ normalizer (M : Set SL))
    (hp : IsPPerfect 2 M) (hne : M ≠ ⊥) : M = complementLocal := by
  let N := M.subgroupOf complementLocal
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hM).mpr hn
  let Q := radical.subgroupOf complementLocal
  let : IsSimpleGroup (complementLocal ⧸ Q) :=
    isSimpleGroup_of_prime_card complementLocal_quotient_card
  have hpN : IsPPerfect 2 N := hp.of_surjective
    (subgroupOfEquivOfLe hM).symm.toMonoidHom (subgroupOfEquivOfLe hM).symm.surjective
  have hnN : N ≠ ⊥ := by
    intro he
    have hm := congrArg (map complementLocal.subtype) he
    rw [map_subgroupOf_eq_of_le hM,Subgroup.map_bot] at hm
    exact hne hm
  have he := eq_top_of_normal_isPPerfect_of_simple_quotient Q
    radical_two_group.comap_subtype complementLocal_twoPerfect N hpN hnN
  have hh := congrArg (map complementLocal.subtype) he
  change (M.subgroupOf complementLocal).map complementLocal.subtype = _ at hh
  simpa only [map_subgroupOf_eq_of_le hM,←MonoidHom.range_eq_map,range_subtype] using hh

@[expose] def complementFlip : SL :=
  ⟨!![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0],by decide⟩

private theorem flip_radical (v : Four) :
    complementFlip * element v * complementFlip⁻¹ = element ![v 2,v 3,v 0,v 1] := by
  have hi : complementFlip⁻¹ = complementFlip := inv_eq_of_mul_eq_one_right (by decide)
  rw [hi]
  apply Subtype.ext
  change complementFlip.val * matrix v * complementFlip.val = matrix _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complementFlip,matrix,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem flip_normalizes : complementFlip ∈ normalizer (complementLocal : Set SL) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [complementLocal,Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨x,⟨v,rfl⟩,rfl⟩
      change complementFlip * element v.toAdd * complementFlip⁻¹ ∈ complementLocal
      rw [flip_radical]
      exact (show radical ≤ complementLocal from le_sup_left) ⟨Multiplicative.ofAdd _,rfl⟩
    · rw [MonoidHom.map_zpowers]
      apply zpowers_le.mpr
      have he : (MulAut.conj complementFlip) complementElement = complementElement⁻¹ := by decide
      change (MulAut.conj complementFlip) complementElement ∈ complementLocal
      rw [he]
      exact complementLocal.inv_mem ((show zpowers complementElement ≤ complementLocal from le_sup_right) (mem_zpowers _))
  · exact (card_map_of_injective (K := complementLocal)
      (f := (MulAut.conj complementFlip).toMonoidHom) (MulAut.conj complementFlip).injective).ge

@[expose] def planeFixer : Subgroup SL := complementLocal ⊔ zpowers complementFlip

private theorem planeFixer_normalizes : planeFixer ≤ normalizer (complementLocal : Set SL) :=
  sup_le complementLocal.le_normalizer (zpowers_le.mpr flip_normalizes)

private theorem planeFixer_quotient_two :
    let : (complementLocal.subgroupOf planeFixer).Normal :=
      (normal_subgroupOf_iff_le_normalizer (show complementLocal ≤ planeFixer from le_sup_left)).mpr
        planeFixer_normalizes
    IsPGroup 2 (planeFixer ⧸ complementLocal.subgroupOf planeFixer) := by
  let : (complementLocal.subgroupOf planeFixer).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show complementLocal ≤ planeFixer from le_sup_left)).mpr
      planeFixer_normalizes
  have hflip : IsPGroup 2 (zpowers complementFlip) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,orderOf_eq_prime (by decide : complementFlip ^ 2 = 1)
      (by decide : complementFlip ≠ 1)]
    decide)
  apply isPGroup_quotient_of_sup_eq_top _ ((zpowers complementFlip).subgroupOf planeFixer)
    hflip.comap_subtype
  rw [←subgroupOf_sup (show complementLocal ≤ planeFixer from le_sup_left)
    (show zpowers complementFlip ≤ planeFixer from le_sup_right)]
  exact subgroupOf_self planeFixer

private theorem binary_block_cases (a b c d : PlaneSpan.Bit) (h : a*d-b*c=1) :
    (a=1 ∧ b=0 ∧ c=0 ∧ d=1) ∨ (a=0 ∧ b=1 ∧ c=1 ∧ d=1) ∨
    (a=1 ∧ b=1 ∧ c=1 ∧ d=0) ∨ (a=0 ∧ b=1 ∧ c=1 ∧ d=0) ∨
    (a=1 ∧ b=0 ∧ c=1 ∧ d=1) ∨ (a=1 ∧ b=1 ∧ c=0 ∧ d=1) := by
  revert a b c d
  decide

/-- The pointwise plane stabilizer has the expected two cosets. -/
theorem mem_planeFixer_of_columns (g : SL)
    (h0 : ∀ i, g.val i 0 = (Pi.single 0 1 : Four) i)
    (h1 : ∀ i, g.val i 1 = (Pi.single 1 1 : Four) i) : g ∈ planeFixer := by
  have he : g.val = !![1,0,g.val 0 2,g.val 0 3; 0,1,g.val 1 2,g.val 1 3;
      0,0,g.val 2 2,g.val 2 3; 0,0,g.val 3 2,g.val 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0,h1]
  have hd : g.val 2 2 * g.val 3 3 - g.val 2 3 * g.val 3 2 = 1 := by
    have hh := g.property
    rw [he] at hh
    rw [Matrix.det_succ_column_zero] at hh
    simpa [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix] using hh
  have hr (v : Four) : element v ∈ planeFixer :=
    (show radical ≤ planeFixer from le_sup_left.trans le_sup_left) ⟨Multiplicative.ofAdd v,rfl⟩
  have hc : complementElement ∈ planeFixer :=
    (show zpowers complementElement ≤ planeFixer from le_sup_right.trans le_sup_left) (mem_zpowers _)
  have ht : complementFlip ∈ planeFixer := (show zpowers complementFlip ≤ planeFixer from le_sup_right) (mem_zpowers _)
  rcases binary_block_cases _ _ _ _ hd with h | h | h | h | h | h
  all_goals rcases h with ⟨ha,hb,hc',hd'⟩
  · have hg : g = element ![g.val 0 2,g.val 1 2,g.val 0 3,g.val 1 3] := by
      apply Subtype.ext
      rw [he]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [element,matrix,ha,hb,hc',hd']
    rw [hg]; exact hr _
  · have hg : g = element ![g.val 0 2+g.val 0 3,g.val 1 2+g.val 1 3,g.val 0 2,g.val 1 2] * complementElement := by
      apply Subtype.ext
      change g.val = matrix _ * complementCubic
      rw [he]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [matrix,complementCubic,Matrix.mul_apply,Fin.sum_univ_succ,ha,hb,hc',hd',add_assoc,CharTwo.add_self_eq_zero]
      all_goals exact (by decide : ∀ a b : PlaneSpan.Bit, b = a + (b+a)) _ _
    rw [hg]; exact planeFixer.mul_mem (hr _) hc
  · have hg : g = element ![g.val 0 3,g.val 1 3,g.val 0 2+g.val 0 3,g.val 1 2+g.val 1 3] * complementElement^2 := by
      apply Subtype.ext
      change g.val = matrix _ * complementCubic^2
      rw [he]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [matrix,complementCubic,pow_two,Matrix.mul_apply,Fin.sum_univ_succ,ha,hb,hc',hd',add_left_comm,CharTwo.add_self_eq_zero]
    rw [hg]; exact planeFixer.mul_mem (hr _) (planeFixer.pow_mem hc 2)
  · have hg : g = element ![g.val 0 3,g.val 1 3,g.val 0 2,g.val 1 2] * complementFlip := by
      apply Subtype.ext
      change g.val = matrix _ * complementFlip.val
      rw [he]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [matrix,complementFlip,Matrix.mul_apply,Fin.sum_univ_succ,ha,hb,hc',hd']
    rw [hg]; exact planeFixer.mul_mem (hr _) ht
  · have hg : g = element ![g.val 0 2+g.val 0 3,g.val 1 2+g.val 1 3,g.val 0 3,g.val 1 3] * (complementElement * complementFlip) := by
      apply Subtype.ext
      change g.val = matrix _ * (complementCubic * complementFlip.val)
      rw [he]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [matrix,complementCubic,complementFlip,Matrix.mul_apply,Fin.sum_univ_succ,ha,hb,hc',hd',add_assoc,CharTwo.add_self_eq_zero]
    rw [hg]; exact planeFixer.mul_mem (hr _) (planeFixer.mul_mem hc ht)
  · have hg : g = element ![g.val 0 2,g.val 1 2,g.val 0 2+g.val 0 3,g.val 1 2+g.val 1 3] * (complementElement^2 * complementFlip) := by
      apply Subtype.ext
      change g.val = matrix _ * (complementCubic^2 * complementFlip.val)
      rw [he]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [matrix,complementCubic,complementFlip,pow_two,Matrix.mul_apply,Fin.sum_univ_succ,ha,hb,hc',hd',CharTwo.add_self_eq_zero]
      all_goals exact (by decide : ∀ a b : PlaneSpan.Bit, b = a + (a+b)) _ _
    rw [hg]; exact planeFixer.mul_mem (hr _) (planeFixer.mul_mem (planeFixer.pow_mem hc 2) ht)

theorem twoPerfect_le_complementLocal_of_columns (M : Subgroup SL) (hp : IsPPerfect 2 M)
    (h0 : ∀ g : M, ∀ i, g.val.val i 0 = (Pi.single 0 1 : Four) i)
    (h1 : ∀ g : M, ∀ i, g.val.val i 1 = (Pi.single 1 1 : Four) i) : M ≤ complementLocal := by
  have hMP : M ≤ planeFixer := fun g hg => mem_planeFixer_of_columns g (h0 ⟨g,hg⟩) (h1 ⟨g,hg⟩)
  let N := complementLocal.subgroupOf planeFixer
  let : N.Normal :=
    (normal_subgroupOf_iff_le_normalizer (show complementLocal ≤ planeFixer from le_sup_left)).mpr
      planeFixer_normalizes
  have hres : pResidual 2 planeFixer ≤ N := sInf_le ⟨inferInstance,planeFixer_quotient_two⟩
  have hpM : IsPPerfect 2 (M.subgroupOf planeFixer) := hp.of_surjective
    (subgroupOfEquivOfLe hMP).symm.toMonoidHom (subgroupOfEquivOfLe hMP).symm.surjective
  exact fun x hx => hres (le_pResidual_of_isPPerfect _ hpM (show
    (⟨x,hMP hx⟩ : planeFixer) ∈ M.subgroupOf planeFixer from hx))

end Representation.BinaryParabolicExteriorSquare.PlaneRadical
