module
public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Theory.GroupTheory.QuaternionCentralProductDiagonal

/-!
# Reductions for involutions on a quaternion central product

An automorphism of square one exchanging the two quaternion factors has the
explicit elementary diagonal as its fixed subgroup. Thus a non-elementary
fixed subgroup forces preservation of both intrinsic quaternion factors.
Furthermore, inner actions on both commuting factors glue to an inner action
on their join, by multiplying the two conjugators.

These reductions isolate the two preserving cases in Janko–Thompson (1970),
§4, printed pp.390–391, case (b)(i). The fixed subgroup is represented by the
equalizer of the automorphism and the identity homomorphism.
-/

namespace Subgroup
open scoped Pointwise

/-- The fixed subgroup of a factor-swapping involutory automorphism is the
quaternion diagonal. -/
public theorem quaternion_diagonal_eq_fixed_of_involution_swap
    {G : Type*} [Group G] (B C : Subgroup G) (θ : B ≃* C)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hsup : B ⊔ C = ⊤) (e : MulAut G) (he : e ^ 2 = 1)
    (hsB : ∀ b : B, e (b : G) = θ b) :
    e.toMonoidHom.eqLocus (MonoidHom.id G) = quaternionDiagonal B C θ hcomm := by
  have he2 (x : G) : e (e x) = x := by
    have hh := DFunLike.congr_fun he x
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have heB (b : B) : e (b : G) = θ b := hsB b
  have heC (c : C) : e (c : G) = (θ.symm c : B) := by
    have hh := congrArg e (heB (θ.symm c))
    simpa only [he2, MulEquiv.apply_symm_apply] using hh.symm
  have heI (x : G) (hx : x ∈ B ⊓ C) : e x = x := by
    have hex : e x ∈ B ⊓ C := by
      constructor
      · rw [heC ⟨x, hx.2⟩]
        exact (θ.symm ⟨x, hx.2⟩).property
      · rw [heB ⟨x, hx.1⟩]
        exact (θ ⟨x, hx.1⟩).property
    by_cases hx1 : x = 1
    · simp [hx1]
    obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : (B ⊓ C : Subgroup G))).mp hinter
    have hxne : (⟨x, hx⟩ : (B ⊓ C : Subgroup G)) ≠ 1 :=
      fun h => hx1 (congrArg Subtype.val h)
    have hexne : (⟨e x, hex⟩ : (B ⊓ C : Subgroup G)) ≠ 1 := by
      intro h
      apply hx1
      apply e.injective
      simpa using congrArg Subtype.val h
    exact congrArg Subtype.val ((hz _ hexne).trans (hz _ hxne).symm)
  apply le_antisymm
  · intro x hx
    have hnorm : B ≤ normalizer (C : Set G) := by
      apply le_trans ?_ (centralizer_le_normalizer _)
      intro b hb c hc
      exact (hcomm b hb c hc).symm
    have hx' : x ∈ (B : Set G) * (C : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right B C hnorm]
      rw [hsup]
      trivial
    obtain ⟨b, hb, c, hc, rfl⟩ := hx'
    have hfixed : e (b*c) = b*c := hx
    let bb : B := ⟨b,hb⟩
    let cc : C := ⟨c,hc⟩
    have heq : (θ bb : G) * (θ.symm cc : G) = b*c := by
      rw [map_mul] at hfixed
      change e (bb : G) * e (cc : G) = b*c at hfixed
      rwa [heB, heC] at hfixed
    let d : G := (θ bb : G)⁻¹ * c
    have hdC : d ∈ C := C.mul_mem (C.inv_mem (θ bb).property) hc
    have hdB : d ∈ B := by
      have hd : d = b⁻¹ * (θ.symm cc : G) := by
        have hbc : b * (θ bb : G) = (θ bb : G) * b := hcomm b hb (θ bb) (θ bb).property
        dsimp [d]
        rw [← mul_left_cancel_iff (a := b)]
        rw [← mul_assoc, (Commute.inv_right hbc).eq, mul_assoc, ← heq]
        simp
      rw [hd]
      exact B.mul_mem (B.inv_mem hb) (θ.symm cc).property
    have hd : d ∈ quaternionDiagonal B C θ hcomm := by
      change d ∈ (quaternionDiagonalHom B C θ hcomm).range ⊔ (B ⊓ C)
      exact (show B ⊓ C ≤ (quaternionDiagonalHom B C θ hcomm).range ⊔ (B ⊓ C)
        from le_sup_right) ⟨hdB, hdC⟩
    have hbdiag : b * (θ bb : G) ∈ quaternionDiagonal B C θ hcomm := by
      change b * (θ bb : G) ∈ (quaternionDiagonalHom B C θ hcomm).range ⊔ (B ⊓ C)
      exact (show (quaternionDiagonalHom B C θ hcomm).range ≤
        (quaternionDiagonalHom B C θ hcomm).range ⊔ (B ⊓ C) from le_sup_left) ⟨bb, rfl⟩
    have hh := (quaternionDiagonal B C θ hcomm).mul_mem hbdiag hd
    simpa [d, mul_assoc] using hh
  · apply sup_le
    · intro x hx
      obtain ⟨b, rfl⟩ := hx
      change e ((b : G) * θ b) = (b : G) * θ b
      rw [map_mul, heB, heC, MulEquiv.symm_apply_apply]
      exact (hcomm b b.property (θ b) (θ b).property).symm
    · intro x hx
      exact heI x hx

/-- A non-elementary fixed subgroup rules out exchanging the two intrinsic
quaternion factors. -/
public theorem quaternion_factors_invariant_of_non_elementary_fixed
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hsup : B ⊔ C = ⊤) (e : MulAut G) (he : e ^ 2 = 1)
    (hfixed : ¬ IsElementaryAbelian 2 (e.toMonoidHom.eqLocus (MonoidHom.id G))) :
    B.map e.toMonoidHom = B ∧ C.map e.toMonoidHom = C := by
  have hne : B ≠ C := by
    intro h
    obtain ⟨model⟩ := hB
    have hcard : Nat.card B = 8 := by
      rw [Nat.card_congr model.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← h, inf_idem, hcard] at hinter
    omega
  have himage (D : Subgroup G) (hD : Nonempty (D ≃* QuaternionGroup 2)) :
      D.map e.toMonoidHom = B ∨ D.map e.toMonoidHom = C := by
    obtain ⟨model⟩ := hD
    exact quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
      ⟨(e.subgroupMap D).symm.trans model⟩ (by rw [hsup]; exact le_top)
  have hBB : B.map e.toMonoidHom = B := by
    rcases himage B hB with hBB | hBC
    · exact hBB
    let θ : B ≃* C := (e.subgroupMap B).trans (MulEquiv.subgroupCongr hBC)
    have hdiag := quaternion_diagonal_eq_fixed_of_involution_swap
      B C θ hinter hcomm hsup e he (fun _ => rfl)
    obtain ⟨model⟩ := hB
    apply False.elim
    apply hfixed
    rw [hdiag]
    exact (quaternion_diagonal_elementary_eight B C model θ hinter hcomm).1
  refine ⟨hBB, ?_⟩
  rcases himage C hC with hCB | hCC
  · exact (hne (map_injective e.injective (hBB.trans hCB.symm))).elim
  · exact hCC

/-- Inner restrictions on two commuting generating factors glue to conjugation
by the product of their conjugators. -/
public theorem exists_conj_of_inner_on_commuting_factors
    {G : Type*} [Group G] (B C : Subgroup G)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hsup : B ⊔ C = ⊤) (e : MulAut G)
    (hB : ∃ b : B, ∀ x : B, e (x : G) = (b : G) * x * (b : G)⁻¹)
    (hC : ∃ c : C, ∀ x : C, e (x : G) = (c : G) * x * (c : G)⁻¹) :
    ∃ g : G, e = MulAut.conj g := by
  obtain ⟨b, hb⟩ := hB
  obtain ⟨c, hc⟩ := hC
  refine ⟨(b : G) * c, ?_⟩
  have hfixB : ∀ x ∈ B, e x = (MulAut.conj ((b : G) * c)) x := by
    intro x hx
    rw [hb ⟨x, hx⟩]
    change (b : G) * x * (b : G)⁻¹ = ((b : G) * c) * x * ((b : G) * c)⁻¹
    rw [mul_inv_rev, mul_assoc (b : G) (c : G) x,
      ← hcomm x hx c c.property]
    group
  have hfixC : ∀ x ∈ C, e x = (MulAut.conj ((b : G) * c)) x := by
    intro x hx
    rw [hc ⟨x, hx⟩, hcomm b b.property c c.property]
    change (c : G) * x * (c : G)⁻¹ = ((c : G) * b) * x * ((c : G) * b)⁻¹
    rw [mul_inv_rev, mul_assoc (c : G) (b : G) x,
      hcomm b b.property x hx]
    group
  ext x
  have hx : x ∈ B ⊔ C := by rw [hsup]; trivial
  exact (show B ⊔ C ≤ e.toMonoidHom.eqLocus
    (MulAut.conj ((b : G) * c)).toMonoidHom from sup_le hfixB hfixC) hx

end Subgroup
