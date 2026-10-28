module
public import Theory.GroupTheory.QuaternionOuterInvolutionReduction
public import Theory.GroupTheory.QuaternionBothOuterInvolutionFixed
public import Theory.GroupTheory.QuaternionMixedInvolutionFixed
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Non-elementary fixed subgroups of outer quaternion-product involutions

Conjugation by an element normalizing a subgroup has a fixed subgroup naturally
isomorphic to the intersection with the element's centralizer. When the subgroup
is self-centralizing, an outside element cannot induce an inner automorphism:
an inner conjugator would differ from it by an element of the centralizer.
For a quaternion central product with non-elementary fixed subgroup, the
intrinsic factor theorem then forces the resulting outer involutory action to
preserve both quaternion factors.

Inner actions on both factors would give an inner action on their product,
whereas outer actions on both factors give elementary fixed points. Thus exactly
one restriction is outer, and the mixed-action calculation gives an extraspecial
fixed subgroup. Transport gives the literal ambient subgroup used in
Janko–Thompson (1970), §4, printed pp.390–391, case (b)(i).
-/

namespace Subgroup

/-- The fixed subgroup of the normalizer action is the ambient centralizer
intersection, viewed inside the centralizer. -/
public def normalizerActionFixedEquiv {P : Type*} [Group P]
    (H : Subgroup P) (t : normalizer (H : Set P)) :
    (H.normalizerMonoidHom t).toMonoidHom.eqLocus (MonoidHom.id H) ≃*
      H.subgroupOf (centralizer ({(t : P)} : Set P)) where
  toFun x := ⟨⟨(x.val : P), by
    rw [mem_centralizer_singleton_iff]
    have hx := congrArg (fun y : H => (y : P)) x.property
    change (t : P) * (x.val : P) * (t : P)⁻¹ = (x.val : P) at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩, x.val.property⟩
  invFun y := ⟨⟨(y.val : P), y.property⟩, by
    apply Subtype.ext
    change (t : P) * (y.val : P) * (t : P)⁻¹ = (y.val : P)
    rw [← mem_centralizer_singleton_iff.mp y.val.property, mul_inv_cancel_right]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- An outside normalizing element acts outerly on a self-centralizing subgroup. -/
public theorem normalizer_action_not_inner_of_self_centralizing
    {P : Type*} [Group P] (H : Subgroup P)
    (hself : centralizer (H : Set P) ≤ H)
    (t : normalizer (H : Set P)) (hout : (t : P) ∉ H) :
    ¬ ∃ h : H, H.normalizerMonoidHom t = MulAut.conj h := by
  rintro ⟨h, hh⟩
  have hc : (h : P)⁻¹ * t ∈ centralizer (H : Set P) := by
    intro x hx
    have he := congrArg (fun a : MulAut H => (a ⟨x, hx⟩ : P)) hh
    change (t : P) * x * (t : P)⁻¹ = (h : P) * x * (h : P)⁻¹ at he
    have hconj : ((h : P)⁻¹ * t) * x * ((h : P)⁻¹ * t)⁻¹ = x := by
      calc
        _ = (h : P)⁻¹ * ((t : P) * x * (t : P)⁻¹) * h := by group
        _ = (h : P)⁻¹ * ((h : P) * x * (h : P)⁻¹) * h := by rw [he]
        _ = x := by group
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  apply hout
  have hm := H.mul_mem h.property (hself hc)
  simpa only [mul_inv_cancel_left] using hm

private theorem elementary_of_mulEquiv {A D : Type*} [Group A] [Group D]
    (e : A ≃* D) (h : IsElementaryAbelian 2 A) : IsElementaryAbelian 2 D := by
  let _ := h
  refine { toIsMulCommutative := ⟨⟨fun x y => e.symm.injective ?_⟩⟩
           exponent_dvd_p := ?_ }
  · simp only [map_mul]
    exact (IsMulCommutative.is_comm (M := A)).comm _ _
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply e.symm.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) _

/-- Transfer extraspecial fixed-point calculations back to the exact ambient
subgroup, without assuming its order or its factor structure. -/
public theorem extraspecial_fixed_of_normalizer_action
    {P : Type*} [Group P] (H : Subgroup P)
    (t : normalizer (H : Set P))
    (h : IsExtraspecial 2
      ((H.normalizerMonoidHom t).toMonoidHom.eqLocus (MonoidHom.id H))) :
    IsExtraspecial 2 (H.subgroupOf (centralizer ({(t : P)} : Set P))) :=
  IsExtraspecial.of_mulEquiv (normalizerActionFixedEquiv H t) h

/-- The intrinsic action attached to an outside involution with non-elementary
fixed subgroup is outer, involutory, and preserves both quaternion factors. -/
public theorem quaternion_outer_involution_action_data
    {P : Type*} [Group P] [Finite P] (H : Subgroup P) [H.Normal]
    (hself : centralizer (H : Set P) ≤ H) (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hsup : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (t : P) (ht : orderOf t = 2) (hout : t ∉ H)
    (hfixed : ¬ IsElementaryAbelian 2 (H.subgroupOf (centralizer ({t} : Set P)))) :
    ∃ e : MulAut H, e ^ 2 = 1 ∧
      B.map e.toMonoidHom = B ∧ C.map e.toMonoidHom = C ∧
      (¬ ∃ h : H, e = MulAut.conj h) ∧
      (¬ IsElementaryAbelian 2 (e.toMonoidHom.eqLocus (MonoidHom.id H))) ∧
      Nonempty (e.toMonoidHom.eqLocus (MonoidHom.id H) ≃*
        H.subgroupOf (centralizer ({t} : Set P))) := by
  let tn : normalizer (H : Set P) := ⟨t, by rw [H.normalizer_eq_top]; trivial⟩
  let e := H.normalizerMonoidHom tn
  have ht2 : tn ^ 2 = 1 := by
    apply Subtype.ext
    exact ht ▸ pow_orderOf_eq_one t
  have he2 : e ^ 2 = 1 := by
    change (H.normalizerMonoidHom tn) ^ 2 = 1
    rw [← map_pow, ht2, map_one]
  have hne : ¬ IsElementaryAbelian 2 (e.toMonoidHom.eqLocus (MonoidHom.id H)) := by
    intro h
    exact hfixed (elementary_of_mulEquiv (normalizerActionFixedEquiv H tn) h)
  obtain ⟨hBB, hCC⟩ := quaternion_factors_invariant_of_non_elementary_fixed
    B C hB hC hinter hcomm hsup e he2 hne
  exact ⟨e, he2, hBB, hCC,
    normalizer_action_not_inner_of_self_centralizing H hself tn hout,
    hne, ⟨normalizerActionFixedEquiv H tn⟩⟩

/-- An outside involution of a self-centralizing quaternion central product has
extraspecial fixed subgroup whenever that subgroup is not elementary abelian.
No preservation of the factors or order of the fixed subgroup is assumed. -/
public theorem extraspecial_fixed_of_quaternion_outer_involution
    {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [H.Normal] [IsExtraspecial 2 H]
    (_hH : Nat.card H = 32) (hself : centralizer (H : Set P) ≤ H)
    (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hsup : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (t : P) (ht : orderOf t = 2) (hout : t ∉ H)
    (hfixed : ¬ IsElementaryAbelian 2 (H.subgroupOf (centralizer ({t} : Set P)))) :
    IsExtraspecial 2 (H.subgroupOf (centralizer ({t} : Set P))) := by
  classical
  obtain ⟨e, he, hBB, hCC, houter, hne, ⟨f⟩⟩ :=
    quaternion_outer_involution_action_data H hself B C hB hC hsup hinter hcomm
      t ht hout hfixed
  apply IsExtraspecial.of_mulEquiv f
  by_cases hBI : ∃ b : B, ∀ x : B, e (x : H) = (b : H) * x * (b : H)⁻¹
  · have hCO : ¬ ∃ c : C, ∀ x : C, e (x : H) = (c : H) * x * (c : H)⁻¹ := by
      intro hCI
      exact houter (exists_conj_of_inner_on_commuting_factors B C hcomm hsup e hBI hCI)
    exact extraspecial_fixed_of_quaternion_mixed_involution C B hC hB
      (by simpa only [sup_comm] using hsup)
      (by simpa only [inf_comm] using hinter) (fun c hc b hb => (hcomm b hb c hc).symm)
      e he hCC hBB hCO hBI
  · by_cases hCI : ∃ c : C, ∀ x : C, e (x : H) = (c : H) * x * (c : H)⁻¹
    · exact extraspecial_fixed_of_quaternion_mixed_involution
        B C hB hC hsup hinter hcomm e he hBB hCC hBI hCI
    · exact (hne (elementary_fixed_of_quaternion_both_outer_involution
        B C hB hC hsup hinter hcomm e he hBB hCC hBI hCI)).elim

end Subgroup
