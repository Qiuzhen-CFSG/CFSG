module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.QuotientAction.Points
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.Transports
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction

/-!
# The full image on the two parabolic core triples

The six points are the actual nonidentity elements of the two embedded
parabolic cores. Numbering each triple gives a block action, hence embeds
the permutation image in S₃ ≀ C₂. Each S₄ factor realizes every permutation
of its own core triple and fixes the other triple pointwise. The image thus
contains a subgroup of order 36. The given factor interchange lies outside
this subgroup; Lagrange's theorem and the wreath bound force image order 72.

The surjective projection from the full lifted overgroup preserves this
image. No kernel identification is used in this calculation.

Source: the wreath-overgroup construction in the proof of Aschbacher–Smith
13.8.16(1), printed p.952 (PDF p.969). Selecting the parabolic pair and
identifying the action kernel remain with the source assembly.
-/

public section
open Subgroup
open Matrix.PSL3Two.ParabolicCoreModel
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.ParabolicPair

private theorem triple_card {K : Type*} [Group K] [Finite K] (hc : Nat.card K = 4) :
    Nat.card {x : K // x ≠ 1} = 3 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card, hc]

private theorem full_core_action {A : Type*} [Group A] [Finite A]
    (P : Subgroup A) (e : P ≃* Equiv.Perm (Fin 4))
    (σ : Equiv.Perm {x : P.pCoreIn 2 // x ≠ 1}) :
    ∃ g : P, ∀ x : {x : P.pCoreIn 2 // x ≠ 1},
      (σ x).val.val = g.val * x.val.val * g.val⁻¹ := by
  let K := pCore 2 P
  let hE := (core_data e).1
  have hc : Nat.card K = 4 := (core_data e).2
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour K := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  let c : K ≃* P.pCoreIn 2 := (pCore 2 P).equivMapOfInjective P.subtype P.subtype_injective
  let b : {x : K // x ≠ 1} ≃ {x : P.pCoreIn 2 // x ≠ 1} :=
    c.toEquiv.subtypeEquiv (by intro x; simp)
  have hsurj : Function.Surjective (autPermHom K) := by
    apply ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨autPermHom_injective K, ?_⟩).2
    rw [IsKleinFour.card_mulAut, Nat.card_perm, triple_card hc]
    decide
  obtain ⟨a, ha⟩ := hsurj (b.symm.permCongrHom σ)
  obtain ⟨q, hq⟩ := (coreQuotientAutEquiv e).surjective a
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (pCore 2 P) q
  refine ⟨g, ?_⟩
  intro x
  have hv := Equiv.congr_fun ha (b.symm x)
  have hh := congrArg (fun y : {x : K // x ≠ 1} => (y.val.val : A)) hv
  have hq' : a = coreQuotientAutEquiv e (QuotientGroup.mk' (pCore 2 P) g) := by rw [hg, hq]
  rw [hq'] at hh
  have he := congrArg (fun y : P => (y : A)) (coreQuotientAutEquiv_mk e g (b.symm x).val)
  change (((coreQuotientAutEquiv e (QuotientGroup.mk' (pCore 2 P) g)) (b.symm x).val).val : A) = _ at he
  have hb (y : {x : P.pCoreIn 2 // x ≠ 1}) : ((b.symm y).val.val : A) = y.val.val := by
    exact congrArg (fun z : {x : P.pCoreIn 2 // x ≠ 1} => z.val.val) (b.apply_symm_apply y)
  change _ = ((b.symm (σ (b (b.symm x)))).val.val : A) at hh
  rw [b.apply_symm_apply] at hh
  rw [hb] at hh
  rw [← hh]
  change (((coreQuotientAutEquiv e (QuotientGroup.mk' (pCore 2 P) g))
    (b.symm x).val).val : A) = _
  rw [he]
  change g.val * ((b.symm x).val.val : A) * g.val⁻¹ = _
  rw [hb]

variable {G : Type*} [Group G] [Finite G] {H L₁ T : Subgroup G} (d : ParabolicPair H L₁ T)

private def swapLabel : C2 := Multiplicative.ofAdd 1
private theorem label_cases (q : C2) : q = 1 ∨ q = swapLabel := by
  revert q
  decide

private noncomputable def sumLabels : (Fin 3 ⊕ Fin 3) ≃ (Fin 3 × C2) where
  toFun := Sum.elim (fun i => (i, 1)) (fun i => (i, swapLabel))
  invFun := fun x => if x.2 = 1 then Sum.inl x.1 else Sum.inr x.1
  left_inv := by rintro (x | x) <;> simp [swapLabel]
  right_inv := by
    rintro ⟨x, q⟩
    rcases label_cases q with rfl | rfl <;> simp [swapLabel]

/-- Number the literal nonidentity core elements, with block labels 1 on the
left and `Multiplicative.ofAdd 1` on the right. -/
noncomputable def corePointLabels : d.CorePoints ≃ (Fin 3 × C2) :=
  d.corePointsEquivSum.trans ((Equiv.sumCongr
    (Finite.equivFinOfCardEq (triple_card d.core_cards.1))
    (Finite.equivFinOfCardEq (triple_card d.core_cards.2))).trans sumLabels)

/-- Every nonidentity element of the embedded left core receives the left label. -/
theorem corePointLabels_left (x : d.CorePoints) (hx : x.val ∈ d.left.pCoreIn 2) :
    (d.corePointLabels x).2 = 1 := by
  let y : {x : d.left.pCoreIn 2 // x ≠ 1} :=
    ⟨⟨x.val, hx⟩, fun he => x.property.1 (congrArg Subtype.val he)⟩
  have he : x = d.corePointsEquivSum.symm (Sum.inl y) := Subtype.ext rfl
  rw [he]
  simp [corePointLabels, sumLabels]

/-- Every nonidentity element of the embedded right core receives the right label. -/
theorem corePointLabels_right (x : d.CorePoints) (hx : x.val ∈ d.right.pCoreIn 2) :
    (d.corePointLabels x).2 = Multiplicative.ofAdd 1 := by
  let y : {x : d.right.pCoreIn 2 // x ≠ 1} :=
    ⟨⟨x.val, hx⟩, fun he => x.property.1 (congrArg Subtype.val he)⟩
  have he : x = d.corePointsEquivSum.symm (Sum.inr y) := Subtype.ext rfl
  rw [he]
  simp [corePointLabels, sumLabels, swapLabel]

/-- Conjugation preserves the two embedded core triples or interchanges them. -/
theorem corePointAction_blocks (g : d.starOvergroup) :
    ∃ q : C2, ∀ x : d.CorePoints,
      (d.corePointLabels (d.corePointAction g x)).2 = q * (d.corePointLabels x).2 := by
  have image_mem (P Q : Subgroup (Source.Hstar H))
      (he : P.map (MulAut.conj g.val).toMonoidHom = Q)
      (x : d.CorePoints) (hx : x.val ∈ P) : (d.corePointAction g x).val ∈ Q := by
    rw [← he]
    exact mem_map_of_mem (MulAut.conj g.val).toMonoidHom hx
  rcases d.starOvergroup_permutes_cores g with hs | hs
  · refine ⟨1, fun x => ?_⟩
    rcases x.property.2 with hx | hx
    · rw [d.corePointLabels_left x hx,
        d.corePointLabels_left _ (image_mem _ _ hs.1 x hx), one_mul]
    · rw [d.corePointLabels_right x hx,
        d.corePointLabels_right _ (image_mem _ _ hs.2 x hx), one_mul]
  · refine ⟨swapLabel, fun x => ?_⟩
    rcases x.property.2 with hx | hx
    · rw [d.corePointLabels_left x hx,
        d.corePointLabels_right _ (image_mem _ _ hs.1 x hx), mul_one]
      rfl
    · rw [d.corePointLabels_right x hx,
        d.corePointLabels_left _ (image_mem _ _ hs.2 x hx)]
      decide

private noncomputable def basePermHom :
    (Equiv.Perm {x : d.left.pCoreIn 2 // x ≠ 1} ×
      Equiv.Perm {x : d.right.pCoreIn 2 // x ≠ 1}) →* Equiv.Perm d.CorePoints :=
  d.corePointsEquivSum.symm.permCongrHom.toMonoidHom.comp (Equiv.Perm.sumCongrHom _ _)

omit [Finite G] in
private theorem basePermHom_injective : Function.Injective d.basePermHom :=
  d.corePointsEquivSum.symm.permCongrHom.injective.comp Equiv.Perm.sumCongrHom_injective

omit [Finite G] in
private theorem basePermHom_inl (σ : Equiv.Perm {x : d.left.pCoreIn 2 // x ≠ 1})
    (τ : Equiv.Perm {x : d.right.pCoreIn 2 // x ≠ 1})
    (x : {x : d.left.pCoreIn 2 // x ≠ 1}) :
    d.basePermHom (σ, τ) (d.corePointsEquivSum.symm (Sum.inl x)) =
      d.corePointsEquivSum.symm (Sum.inl (σ x)) := by
  simp [basePermHom, Equiv.permCongr_apply]

omit [Finite G] in
private theorem basePermHom_inr (σ : Equiv.Perm {x : d.left.pCoreIn 2 // x ≠ 1})
    (τ : Equiv.Perm {x : d.right.pCoreIn 2 // x ≠ 1})
    (x : {x : d.right.pCoreIn 2 // x ≠ 1}) :
    d.basePermHom (σ, τ) (d.corePointsEquivSum.symm (Sum.inr x)) =
      d.corePointsEquivSum.symm (Sum.inr (τ x)) := by
  simp [basePermHom, Equiv.permCongr_apply]

private theorem left_perms_mem (σ : Equiv.Perm {x : d.left.pCoreIn 2 // x ≠ 1}) :
    d.basePermHom (σ, 1) ∈ d.corePointAction.range := by
  obtain ⟨g, hg⟩ := full_core_action d.left d.leftEquiv σ
  have hgle : d.left ≤ d.starOvergroup := le_sup_left.trans le_sup_left
  refine ⟨⟨g.val, hgle g.property⟩, ?_⟩
  apply Equiv.ext
  intro z
  obtain ⟨x, rfl⟩ := d.corePointsEquivSum.symm.surjective z
  cases x with
  | inl x =>
    rw [d.basePermHom_inl]
    apply Subtype.ext
    rw [d.corePointAction_apply, d.corePointsEquivSum_symm_inl,
      d.corePointsEquivSum_symm_inl, hg]
  | inr x =>
    rw [d.basePermHom_inr]
    apply Subtype.ext
    rw [d.corePointAction_apply, d.corePointsEquivSum_symm_inr,
      d.corePointsEquivSum_symm_inr]
    change g.val * x.val.val * g.val⁻¹ = x.val.val
    rw [(d.commute g.val g.property x.val.val (pCoreIn_le 2 d.right x.val.property)).eq]
    exact mul_inv_cancel_right _ _

private theorem right_perms_mem (τ : Equiv.Perm {x : d.right.pCoreIn 2 // x ≠ 1}) :
    d.basePermHom (1, τ) ∈ d.corePointAction.range := by
  obtain ⟨g, hg⟩ := full_core_action d.right d.rightEquiv τ
  have hgle : d.right ≤ d.starOvergroup := le_sup_right.trans le_sup_left
  refine ⟨⟨g.val, hgle g.property⟩, ?_⟩
  apply Equiv.ext
  intro z
  obtain ⟨x, rfl⟩ := d.corePointsEquivSum.symm.surjective z
  cases x with
  | inl x =>
    rw [d.basePermHom_inl]
    apply Subtype.ext
    rw [d.corePointAction_apply, d.corePointsEquivSum_symm_inl,
      d.corePointsEquivSum_symm_inl]
    change g.val * x.val.val * g.val⁻¹ = x.val.val
    rw [← (d.commute x.val.val (pCoreIn_le 2 d.left x.val.property) g.val g.property).eq]
    exact mul_inv_cancel_right _ _
  | inr x =>
    rw [d.basePermHom_inr]
    apply Subtype.ext
    rw [d.corePointAction_apply, d.corePointsEquivSum_symm_inr,
      d.corePointsEquivSum_symm_inr, hg]

private theorem base_range_le : d.basePermHom.range ≤ d.corePointAction.range := by
  rintro _ ⟨⟨σ, τ⟩, rfl⟩
  have h := d.corePointAction.range.mul_mem (d.left_perms_mem σ) (d.right_perms_mem τ)
  simpa only [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] using h

private theorem base_range_card : Nat.card d.basePermHom.range = 36 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective d.basePermHom_injective).toEquiv,
    Nat.card_prod, Nat.card_perm, Nat.card_perm,
    triple_card d.core_cards.1, triple_card d.core_cards.2]
  decide

private theorem base_range_ne : d.basePermHom.range ≠ d.corePointAction.range := by
  obtain ⟨t, ht, hm⟩ := d.moves
  let g : d.starOvergroup := ⟨t, (show Source.starImage H T ≤ d.starOvergroup from le_sup_right) ht⟩
  let x : {x : d.left.pCoreIn 2 // x ≠ 1} :=
    (Finite.equivFinOfCardEq (triple_card d.core_cards.1)).symm 0
  let z := d.corePointsEquivSum.symm (Sum.inl x)
  have hmap : (d.left.pCoreIn 2).map (MulAut.conj t).toMonoidHom =
      d.right.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 d.left _ (MulAut.conj t).injective, hm]
  have hr : (d.corePointAction g z).val ∈ d.right.pCoreIn 2 := by
    have h := mem_map_of_mem (MulAut.conj t).toMonoidHom x.val.property
    rw [hmap] at h
    exact h
  intro he
  have hmem : d.corePointAction g ∈ d.basePermHom.range := by
    rw [he]
    exact ⟨g, rfl⟩
  obtain ⟨⟨σ, τ⟩, hp⟩ := hmem
  have hl : (d.corePointAction g z).val ∈ d.left.pCoreIn 2 := by
    rw [← hp]
    change (d.basePermHom (σ, τ) (d.corePointsEquivSum.symm (Sum.inl x))).val ∈ _
    rw [d.basePermHom_inl, d.corePointsEquivSum_symm_inl]
    exact (σ x).val.property
  exact (d.corePointAction g z).property.1 (Subgroup.disjoint_def.mp d.disjoint
    (pCoreIn_le 2 d.left hl) (pCoreIn_le 2 d.right hr))

private theorem image_card_le : Nat.card d.corePointAction.range ≤ 72 := by
  obtain ⟨f, hf⟩ := RegularWreathProduct.exists_embedding_range_of_two_blocks
    d.corePointAction d.corePointLabels d.corePointAction_blocks
  obtain ⟨es⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let ew := RegularWreathProduct.congr es (MulEquiv.refl C2)
  have h := Nat.card_le_card_of_injective (ew ∘ f) (ew.injective.comp hf)
  have hc : Nat.card S3Wreath = 72 := by
    rw [Nat.card_congr (RegularWreathProduct.equivProd _ _), Nat.card_prod,
      Nat.card_fun, Nat.card_perm]
    norm_num [C2, Nat.factorial]
  exact hc ▸ h

/-- The literal action realizes all 72 permutations preserving the pair of triples. -/
theorem corePointAction_range_card : Nat.card d.corePointAction.range = 72 := by
  have hd : 36 ∣ Nat.card d.corePointAction.range :=
    d.base_range_card ▸ Subgroup.card_dvd_of_le d.base_range_le
  have hgt : 36 < Nat.card d.corePointAction.range := by
    by_contra hn
    apply d.base_range_ne
    exact Subgroup.eq_of_le_of_card_ge d.base_range_le (by rw [d.base_range_card]; omega)
  have hle := d.image_card_le
  obtain ⟨k, hk⟩ := hd
  omega

/-- The full inverse image in H preserves or interchanges the same two blocks. -/
theorem liftedCorePointAction_blocks (g : d.overgroup) :
    ∃ q : C2, ∀ x : d.CorePoints,
      (d.corePointLabels (d.liftedCorePointAction g x)).2 = q * (d.corePointLabels x).2 :=
  d.corePointAction_blocks (d.starProjection g)

/-- Surjectivity of the projection preserves the full 72-element image. -/
theorem liftedCorePointAction_range_card : Nat.card d.liftedCorePointAction.range = 72 := by
  rw [d.liftedCorePointAction_range, d.corePointAction_range_card]

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.ParabolicPair
end
