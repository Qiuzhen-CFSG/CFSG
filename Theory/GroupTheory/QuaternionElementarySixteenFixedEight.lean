module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightCommutingOuter
public import Theory.GroupTheory.QuaternionOuterInvolutionFixed
public import Theory.GroupTheory.QuaternionFixedEightNormal
public import Theory.GroupTheory.PGroup.ExtraspecialSmallOrder

/-!
# Fixed eight of the second outside involution

Let H be a self-centralizing normal extraspecial quaternion central product
of order thirty-two. Suppose an outside involution t has fixed four W in H,
and j is a commuting outside involution not in W⟨t⟩. If the extension has no
normal elementary subgroup of order at least eight, the fixed subgroup of j
in H is nonabelian of order eight.

For an outer involution with elementary fixed points of order other than eight,
both intrinsic quaternion factors are invariant and both restrictions are
outer. Indeed, swapping gives fixed eight, mixed restrictions give nonabelian
fixed points, and two inner restrictions glue to an inner action. Apply this
to t and, hypothetically, to j; a fixed elementary eight for j is excluded by
its proved ambient normality. Commuting outer involutions on each quaternion
factor have inner product, so tj acts inner on H. Self-centrality forces tj
into H, contradicting j ∉ W⟨t⟩. Thus j has non-elementary fixed points; the
existing outer-involution theorem gives an extraspecial proper subgroup of H,
and the small extraspecial order bound gives order eight.

Source: Janko–Thompson (1970), §4, case (b)(ii), last paragraph of printed p.391,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Subgroup

private theorem not_commutative_of_extraspecial {G : Type*} [Group G]
    (h : IsExtraspecial 2 G) : ¬ IsMulCommutative G := by
  intro hc
  let : Nontrivial (G ⧸ center G) := h.quotient_nontrivial
  exact QuotientGroup.nontrivial_iff.mp inferInstance (center_eq_top_iff.mpr hc)

private theorem factors_outer_of_elementary_fixed_not_eight
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hsup : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (e : MulAut G) (he : e^2=1) (ho : ¬ ∃ b, e = MulAut.conj b)
    (hel : IsElementaryAbelian 2 (e.toMonoidHom.eqLocus (MonoidHom.id G)))
    (hcard : Nat.card (e.toMonoidHom.eqLocus (MonoidHom.id G)) ≠ 8) :
    B.map e.toMonoidHom = B ∧ C.map e.toMonoidHom = C ∧
      (¬ ∃ b : B, ∀ x : B, e (x : G) = (b : G)*x*(b : G)⁻¹) ∧
      (¬ ∃ c : C, ∀ x : C, e (x : G) = (c : G)*x*(c : G)⁻¹) := by
  have hne : B ≠ C := by
    intro hh
    obtain ⟨b⟩ := hB
    have hc : Nat.card B = 8 := by
      rw [Nat.card_congr b.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← hh, inf_idem, hc] at hinter
    omega
  have hBB : B.map e.toMonoidHom = B := by
    obtain ⟨b⟩ := hB
    rcases quaternion_subgroup_eq_factor B C (B.map e.toMonoidHom) ⟨b⟩ hC hinter hcomm
      ⟨(e.subgroupMap B).symm.trans b⟩ (by rw [hsup]; exact le_top) with h | h
    · exact h
    let θ : B ≃* C := (e.subgroupMap B).trans (MulEquiv.subgroupCongr h)
    apply False.elim
    apply hcard
    rw [quaternion_diagonal_eq_fixed_of_involution_swap B C θ hinter hcomm hsup e he
      (fun _ => rfl)]
    exact (quaternion_diagonal_elementary_eight B C b θ hinter hcomm).2.1
  have hCC : C.map e.toMonoidHom = C := by
    obtain ⟨c⟩ := hC
    rcases quaternion_subgroup_eq_factor B C (C.map e.toMonoidHom) hB ⟨c⟩ hinter hcomm
      ⟨(e.subgroupMap C).symm.trans c⟩ (by rw [hsup]; exact le_top) with h | h
    · exact (hne (map_injective e.injective (hBB.trans h.symm))).elim
    · exact h
  have hBO : ¬ ∃ b : B, ∀ x : B, e (x : G) = (b : G)*x*(b : G)⁻¹ := by
    intro hBI
    have hCO : ¬ ∃ c : C, ∀ x : C, e (x : G) = (c : G)*x*(c : G)⁻¹ := by
      intro hCI
      exact ho (exists_conj_of_inner_on_commuting_factors B C hcomm hsup e hBI hCI)
    exact not_commutative_of_extraspecial
      (extraspecial_fixed_of_quaternion_mixed_involution C B hC hB
        (by simpa only [sup_comm] using hsup) (by simpa only [inf_comm] using hinter)
        (fun c hc b hb => (hcomm b hb c hc).symm) e he hCC hBB hCO hBI)
      hel.toIsMulCommutative
  refine ⟨hBB, hCC, hBO, ?_⟩
  intro hCI
  exact not_commutative_of_extraspecial
    (extraspecial_fixed_of_quaternion_mixed_involution B C hB hC hsup hinter hcomm
      e he hBB hCC hBO hCI) hel.toIsMulCommutative

private theorem inner_product_on_factor
    {G : Type*} [Group G] (B : Subgroup G)
    (model : B ≃* QuaternionGroup 2) (e f : MulAut G)
    (he : e^2=1) (hf : f^2=1) (hef : Commute e f)
    (heB : B.map e.toMonoidHom = B) (hfB : B.map f.toMonoidHom = B)
    (heo : ¬ ∃ b : B, ∀ x : B, e (x : G) = (b : G)*x*(b : G)⁻¹)
    (hfo : ¬ ∃ b : B, ∀ x : B, f (x : G) = (b : G)*x*(b : G)⁻¹) :
    ∃ b : B, ∀ x : B, (e*f) (x : G) = (b : G)*x*(b : G)⁻¹ := by
  let a : MulAut B := (e.subgroupMap B).trans (MulEquiv.subgroupCongr heB)
  let b : MulAut B := (f.subgroupMap B).trans (MulEquiv.subgroupCongr hfB)
  have ha (x : B) : (a x : G) = e x := rfl
  have hb (x : B) : (b x : G) = f x := rfl
  have ha2 : a^2=1 := by
    ext x
    change (a (a x) : G) = x
    rw [ha, ha]
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun he (x : G)
  have hb2 : b^2=1 := by
    ext x
    change (b (b x) : G) = x
    rw [hb, hb]
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hf (x : G)
  have hao : ¬ ∃ z, a = MulAut.conj z := by
    rintro ⟨z, hz⟩
    exact heo ⟨z, fun x => congrArg Subtype.val (DFunLike.congr_fun hz x)⟩
  have hbo : ¬ ∃ z, b = MulAut.conj z := by
    rintro ⟨z, hz⟩
    exact hfo ⟨z, fun x => congrArg Subtype.val (DFunLike.congr_fun hz x)⟩
  have hab : Commute a b := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change e (f x) = f (e x)
    exact DFunLike.congr_fun hef.eq (x : G)
  obtain ⟨z, hz⟩ := QuaternionGroup.exists_conj_of_commuting_outer_involutions_of_equiv
    model a b ha2 hb2 hao hbo hab
  exact ⟨z, fun x => congrArg Subtype.val (DFunLike.congr_fun hz x)⟩


private theorem elementary_transport {A D : Type*} [Group A] [Group D]
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

private def subgroupOfInfEquiv {P : Type*} [Group P] (H K : Subgroup P) :
    H.subgroupOf K ≃* (H ⊓ K : Subgroup P) where
  toFun x := ⟨x.val, x.property, x.val.property⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  map_mul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private def actionFixedInfEquiv {P : Type*} [Group P]
    (H : Subgroup P) (t : normalizer (H : Set P)) :
    (H.normalizerMonoidHom t).toMonoidHom.eqLocus (MonoidHom.id H) ≃*
      (H ⊓ centralizer ({(t : P)} : Set P) : Subgroup P) :=
  (normalizerActionFixedEquiv H t).trans (subgroupOfInfEquiv H _)

private theorem action_square_one {P : Type*} [Group P]
    (H : Subgroup P) (t : normalizer (H : Set P)) (ht : (t : P)^2=1) :
    (H.normalizerMonoidHom t)^2=1 := by
  have ht' : t^2=1 := Subtype.ext ht
  rw [← map_pow, ht', map_one]

/-- The second outside involution commuting with an elementary-sixteen
centralizer involution fixes a nonabelian subgroup of order eight in the
self-centralizing quaternion core. The exclusion hypothesis concerns only
normal elementary abelian subgroups. -/
public theorem quaternion_elementary_sixteen_second_fixed_eight
    {P : Type*} [Group P] [Finite P] (_hP : IsPGroup 2 P)
    (H : Subgroup P) [H.Normal] [IsExtraspecial 2 H]
    (hH : Nat.card H = 32) (hself : centralizer (H : Set P) ≤ H)
    (_hindex : H.index = 4) (hquot : IsElementaryAbelian 2 (P ⧸ H))
    (hno : ¬ ∃ F : Subgroup P, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (B C : Subgroup H) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2)) (hsup : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (t : P) (ht : orderOf t = 2) (hout : t ∉ H)
    (_hE : IsElementaryAbelian 2 (centralizer ({t} : Set P)))
    (_hEcard : Nat.card (centralizer ({t} : Set P)) = 16)
    (hWE : H ⊓ centralizer ({t} : Set P) = W)
    (j : P) (hj : orderOf j = 2) (hjt : j ∈ centralizer ({t} : Set P))
    (hjW : j ∉ W ⊔ zpowers t) (hjout : j ∉ H) :
    ¬ IsMulCommutative (H ⊓ centralizer ({j} : Set P) : Subgroup P) ∧
      Nat.card (H ⊓ centralizer ({j} : Set P) : Subgroup P) = 8 := by
  classical
  let : IsElementaryAbelian 2 (P ⧸ H) := hquot
  let tn : normalizer (H : Set P) := ⟨t, by rw [H.normalizer_eq_top]; trivial⟩
  let jn : normalizer (H : Set P) := ⟨j, by rw [H.normalizer_eq_top]; trivial⟩
  let e := H.normalizerMonoidHom tn
  let f := H.normalizerMonoidHom jn
  have ht2 : t^2=1 := ht ▸ pow_orderOf_eq_one t
  have hj2 : j^2=1 := hj ▸ pow_orderOf_eq_one j
  have he : e^2=1 := action_square_one H tn ht2
  have hf : f^2=1 := action_square_one H jn hj2
  have hef : Commute e f := by
    apply Commute.map _ H.normalizerMonoidHom
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp hjt).symm
  have heo := normalizer_action_not_inner_of_self_centralizing H hself tn hout
  have hfo := normalizer_action_not_inner_of_self_centralizing H hself jn hjout
  have hequiv := (actionFixedInfEquiv H tn).trans (MulEquiv.subgroupCongr hWE)
  have helem : IsElementaryAbelian 2 (e.toMonoidHom.eqLocus (MonoidHom.id H)) :=
    elementary_transport hequiv.symm inferInstance
  have hecard : Nat.card (e.toMonoidHom.eqLocus (MonoidHom.id H)) ≠ 8 := by
    rw [Nat.card_congr hequiv.toEquiv, hW]
    decide
  obtain ⟨heB, heC, heBO, heCO⟩ := factors_outer_of_elementary_fixed_not_eight
    B C hB hC hsup hinter hcomm e he heo helem hecard
  have hne : ¬ IsElementaryAbelian 2 (H ⊓ centralizer ({j} : Set P) : Subgroup P) := by
    intro hjelem
    have hjcard : Nat.card (H ⊓ centralizer ({j} : Set P) : Subgroup P) ≠ 8 := by
      intro hcard
      exact hno ⟨_, quaternion_fixed_eight_normal H hH B C hB hC hsup hinter hcomm
        j hj2 hjelem hcard, hjelem, by omega⟩
    have hfelem : IsElementaryAbelian 2 (f.toMonoidHom.eqLocus (MonoidHom.id H)) :=
      elementary_transport (actionFixedInfEquiv H jn).symm hjelem
    have hfcard : Nat.card (f.toMonoidHom.eqLocus (MonoidHom.id H)) ≠ 8 := by
      rwa [Nat.card_congr (actionFixedInfEquiv H jn).toEquiv]
    obtain ⟨hfB, hfC, hfBO, hfCO⟩ := factors_outer_of_elementary_fixed_not_eight
      B C hB hC hsup hinter hcomm f hf hfo hfelem hfcard
    obtain ⟨modelB⟩ := hB
    obtain ⟨modelC⟩ := hC
    have hiB := inner_product_on_factor B modelB e f he hf hef heB hfB heBO hfBO
    have hiC := inner_product_on_factor C modelC e f he hf hef heC hfC heCO hfCO
    have hi := exists_conj_of_inner_on_commuting_factors B C hcomm hsup (e*f) hiB hiC
    have htjout : t*j ∉ H := by
      intro htjH
      have htjE : t*j ∈ centralizer ({t} : Set P) :=
        (centralizer ({t} : Set P)).mul_mem (mem_centralizer_singleton_iff.mpr rfl) hjt
      have htjW : t*j ∈ W := hWE ▸ ⟨htjH, htjE⟩
      apply hjW
      have htmem : t ∈ W ⊔ zpowers t := (show zpowers t ≤ W ⊔ zpowers t from le_sup_right) (mem_zpowers t)
      have hm := (W ⊔ zpowers t).mul_mem ((W ⊔ zpowers t).inv_mem htmem)
        ((show W ≤ W ⊔ zpowers t from le_sup_left) htjW)
      simpa only [inv_mul_cancel_left] using hm
    apply normalizer_action_not_inner_of_self_centralizing H hself (tn*jn) htjout
    simpa only [map_mul] using hi
  have hsubne : ¬ IsElementaryAbelian 2 (H.subgroupOf (centralizer ({j} : Set P))) := by
    intro hh
    exact hne (elementary_transport (subgroupOfInfEquiv H _) hh)
  have hspecial := extraspecial_fixed_of_quaternion_outer_involution H hH hself B C
    hB hC hsup hinter hcomm j hj hjout hsubne
  let : IsExtraspecial 2 (H ⊓ centralizer ({j} : Set P) : Subgroup P) :=
    IsExtraspecial.of_mulEquiv (subgroupOfInfEquiv H _) hspecial
  refine ⟨not_commutative_of_extraspecial inferInstance, ?_⟩
  apply IsExtraspecial.card_eq_eight_of_card_lt_thirty_two
  have hle : H ⊓ centralizer ({j} : Set P) ≤ H := inf_le_left
  have hc := card_le_of_le hle
  have hneq : Nat.card (H ⊓ centralizer ({j} : Set P) : Subgroup P) ≠ Nat.card H := by
    intro hh
    have heq := eq_of_le_of_card_ge hle hh.ge
    apply hjout
    apply hself
    intro x hx
    have hxj : x ∈ centralizer ({j} : Set P) := (heq.symm ▸ hx).2
    exact mem_centralizer_singleton_iff.mp hxj
  omega
end Subgroup
