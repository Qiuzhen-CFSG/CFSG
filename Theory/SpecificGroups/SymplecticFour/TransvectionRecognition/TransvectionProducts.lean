module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.TransvectionFusion

/-!
# Products of commuting symplectic transvections

Two commuting characteristic-two transvections with distinct moved lines
have a rank-two product of type c₂. A vector annihilating one center but not
the other isolates each summand in the displacement space, and also proves
that the product does not preserve orthogonality of every vector with its
image. The exact coset corollary places this c₂ involution in the specified
subgroup, with no ambient finiteness or irreducibility assumption.

Source: Aschbacher--Smith G.4.5(3) and the preliminary claim in G.4.9,
printed pp.339 and 341. The existence of a suitable commuting coset
representative is a separate geometric step.
-/

public noncomputable section

open Subgroup Module
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2]

private theorem form_symm' (x y : Vector F) : form F x y=form F y x := by
  simpa only [CharTwo.neg_eq] using TwoLocalCover.form_alternating.neg_eq x y

private theorem exists_separating_vector (u v : Vector F)
    (hu : u∉Submodule.span F ({v} : Set (Vector F))) :
    ∃x, form F v x=0 ∧ form F u x≠0 := by
  by_contra! hn
  apply hu
  rw [←(form F).orthogonal_orthogonal TwoLocalCover.form_nondegenerate
    TwoLocalCover.form_alternating.isRefl (Submodule.span F ({v} : Set (Vector F)))]
  intro x hx
  rw [form_symm']
  exact hn x (hx v (Submodule.subset_span (Set.mem_singleton v)))

omit [CharP F 2] in
theorem movedSpace_eq_span_center (a : Sp F) (u : Vector F) (c : F)
    (hu : u≠0) (hc : c≠0) (ha : ∀x, a • x=x+(c*form F u x) • u) :
    movedSpace a=Submodule.span F ({u} : Set (Vector F)) := by
  obtain ⟨x,hx⟩ : ∃x, form F u x≠0 := by
    by_contra! hn
    exact hu (TwoLocalCover.form_nondegenerate.1 u hn)
  apply le_antisymm
  · rintro y ⟨z,rfl⟩
    change a • z-z∈_
    rw [ha,add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · apply Submodule.span_le.mpr
    intro y hy
    have hy : y=u := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨(c*form F u x)⁻¹ • x,?_⟩
    change a • ((c*form F u x)⁻¹ • x)-((c*form F u x)⁻¹ • x) = u
    rw [ha,add_sub_cancel_left]
    simp only [map_smul,smul_eq_mul]
    have hn : c*form F u x≠0 := mul_ne_zero hc hx
    have he : c*((c*form F u x)⁻¹*form F u x)=1 := by
      rw [←mul_assoc,mul_comm c, mul_assoc,inv_mul_cancel₀ hn]
    rw [he,one_smul]

private theorem pairing_zero_of_commute (a b : Sp F) (u v : Vector F) (c d : F)
    (hu : u≠0) (hv : v≠0) (hc : c≠0) (hd : d≠0)
    (ha : ∀x, a • x=x+(c*form F u x) • u)
    (hb : ∀x, b • x=x+(d*form F v x) • v) (hab : Commute a b) :
    form F u v=0 := by
  have hfix := fixes_center_of_commute b a v d hv hd hb hab
  rw [ha] at hfix
  have hs : (c*form F u v) • u=0 := add_left_cancel (hfix.trans (add_zero v).symm)
  exact (mul_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hu)).resolve_left hc

omit [CharP F 2] in
private theorem product_formula (a b : Sp F) (u v : Vector F) (c d : F)
    (ha : ∀x, a • x=x+(c*form F u x) • u)
    (hb : ∀x, b • x=x+(d*form F v x) • v) (huv : form F u v=0) :
    ∀x, (a*b) • x=x+(c*form F u x) • u+(d*form F v x) • v := by
  intro x
  rw [mul_smul,hb,ha]
  simp only [map_add,map_smul,smul_eq_mul,huv,mul_zero,add_zero]
  abel

theorem isC2_product_of_commute_distinct_movedSpace (a b : Sp F)
    (ha : IsB1 a) (hb : IsB1 b) (hab : Commute a b)
    (hne : movedSpace a≠movedSpace b) : IsC2 (a*b) := by
  obtain ⟨u,c,hu,hc,haform⟩ := rank_one_formula a ha
  obtain ⟨v,d,hv,hd,hbform⟩ := rank_one_formula b hb
  have hma := movedSpace_eq_span_center a u c hu hc haform
  have hmb := movedSpace_eq_span_center b v d hv hd hbform
  have huv : u∉Submodule.span F ({v} : Set (Vector F)) := by
    intro h
    apply hne
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [hma,hmb]
      exact Submodule.span_le.mpr (by rintro z rfl; exact h)
    · exact ha.2.trans hb.2.symm
  have hvu : v∉Submodule.span F ({u} : Set (Vector F)) := by
    intro h
    apply hne
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [hma,hmb]
      exact Submodule.span_le.mpr (by rintro z rfl; exact h)
    · exact hb.2.trans ha.2.symm
  obtain ⟨x,hvx,hux⟩ := exists_separating_vector u v huv
  obtain ⟨y,huy,hvy⟩ := exists_separating_vector v u hvu
  have hzero := pairing_zero_of_commute a b u v c d hu hv hc hd haform hbform hab
  have hformula := product_formula a b u v c d haform hbform hzero
  have hum : u∈movedSpace (a*b) := by
    have hm : (c*form F u x) • u∈movedSpace (a*b) := by
      refine ⟨x,?_⟩
      change (a*b) • x-x=_
      rw [hformula,hvx,mul_zero,zero_smul,add_zero,add_sub_cancel_left]
    have h := Submodule.smul_mem (movedSpace (a*b)) (c*form F u x)⁻¹ hm
    simpa only [smul_smul,inv_mul_cancel₀ (mul_ne_zero hc hux),one_smul] using h
  have hvm : v∈movedSpace (a*b) := by
    have hm : (d*form F v y) • v∈movedSpace (a*b) := by
      refine ⟨y,?_⟩
      change (a*b) • y-y=_
      rw [hformula,huy,mul_zero,zero_smul,add_zero,add_sub_cancel_left]
    have h := Submodule.smul_mem (movedSpace (a*b)) (d*form F v y)⁻¹ hm
    simpa only [smul_smul,inv_mul_cancel₀ (mul_ne_zero hd hvy),one_smul] using h
  have hrange : movedSpace (a*b)=Submodule.span F (Set.range ![u,v]) := by
    apply le_antisymm
    · rintro z ⟨w,rfl⟩
      change (a*b) • w-w∈_
      rw [hformula]
      have he : w+(c*form F u w) • u+(d*form F v w) • v-w=
          (c*form F u w) • u+(d*form F v w) • v := by abel
      rw [he]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1,rfl⟩))
    · apply Submodule.span_le.mpr
      rintro z ⟨i,rfl⟩
      fin_cases i
      · exact hum
      · exact hvm
  have hli : LinearIndependent F ![u,v] := (LinearIndependent.pair_iff' hu).mpr
    (fun k hk => hvu (Submodule.mem_span_singleton.mpr ⟨k,hk⟩))
  have hrank : finrank F (movedSpace (a*b))=2 := by
    rw [hrange]
    simpa only [Fintype.card_fin] using finrank_span_eq_card hli
  have hsq : (a*b)^2=1 := by
    rw [hab.mul_pow]
    have has : a^2=1 := by simpa only [ha.1] using pow_orderOf_eq_one a
    have hbs : b^2=1 := by simpa only [hb.1] using pow_orderOf_eq_one b
    rw [has,hbs,mul_one]
  have hn : a*b≠1 := by
    intro he
    rw [he] at hrank
    have hm : movedSpace (1 : Sp F)=⊥ := by
      apply le_bot_iff.mp
      rintro z ⟨w,rfl⟩
      change (1 : Sp F) • w-w=0
      simp
    rw [hm,finrank_bot] at hrank
    omega
  refine ⟨orderOf_eq_prime hsq hn,hrank,x,?_⟩
  rw [hformula,hvx,mul_zero,zero_smul,add_zero,map_add,
    TwoLocalCover.form_alternating.self_eq_zero,zero_add,map_smul,smul_eq_mul,
    form_symm' x u]
  exact mul_ne_zero (mul_ne_zero hc hux) hux

/-- The literal coset condition puts the resulting c₂ involution in X. -/
theorem isC2_mem_of_commuting_coset (X : Subgroup (Sp F)) (a b : Sp F)
    (ha : IsB1 a) (hb : IsB1 b) (hab : Commute a b)
    (hne : movedSpace a≠movedSpace b) (hcoset : a⁻¹*b∈X) :
    a*b∈X ∧ IsC2 (a*b) := by
  have has : a*a=1 := by simpa only [ha.1,pow_two] using pow_orderOf_eq_one a
  have hai : a⁻¹=a := inv_eq_iff_mul_eq_one.mpr has
  exact ⟨by simpa only [hai] using hcoset,
    isC2_product_of_commute_distinct_movedSpace a b ha hb hab hne⟩

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
