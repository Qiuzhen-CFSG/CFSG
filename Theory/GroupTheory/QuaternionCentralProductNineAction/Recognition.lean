module
public import Theory.GroupTheory.QuaternionCentralProductNineAction.NonInversion
public import Theory.GroupTheory.QuaternionCentralProductNineAction.Quotient

/-!
# A fixed cubic element in the exceptional quaternion outer action

Let `Q` be a normal self-centralizing quaternion central product of order 32
in a group of order 1152. An elementary sixteen meeting `Q` in an elementary
eight has image of order two modulo `Q`. Its outside elements interchange
the quaternion factors. A Sylow three-subgroup supplies independent cubic
actors, whose image is elementary of order nine. The factor stabilizer has
index two, so that image is normal by Sylow counting in the quotient of order
36. Factor interchange cannot invert the cubic image; an involution on an
abelian three-group which is not inversion has a nontrivial fixed point.

Source: Aschbacher–Smith, §5.3.7, printed p.661 (PDF p.678).
-/

namespace Subgroup

private theorem fixed_cubic_of_normal_elementary_noninversion
    {K : Type*} [Group K] (E : Subgroup K) [E.Normal]
    [IsElementaryAbelian 3 E] (t : K) (ht : t ^ 2 = 1)
    (hnot : ∃ a : E, t * a * t⁻¹ ≠ (a : K)⁻¹) :
    ∃ r : K, r ∈ centralizer (zpowers t : Set K) ∧ r ≠ 1 ∧ r ^ 3 = 1 := by
  let σ : MulAut E := MulAut.conjNormal t
  have hσ : σ ^ 2 = 1 := by
    change (MulAut.conjNormal t : MulAut E) ^ 2 = 1
    rw [← map_pow, ht, map_one]
  have hσ2 (a : E) : σ (σ a) = a := by
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hσ a
  obtain ⟨a, ha⟩ := hnot
  let r : E := a * σ a
  have hr : r ≠ 1 := by
    intro hh
    have he : σ a = a⁻¹ := eq_inv_of_mul_eq_one_right hh
    exact ha (congrArg Subtype.val he)
  have hfix : σ r = r := by
    change σ (a * σ a) = a * σ a
    rw [map_mul, hσ2]
    exact IsMulCommutative.is_comm.comm _ _
  have hc : Commute t (r : K) := by
    have hh := congrArg Subtype.val hfix
    change t * (r : K) * t⁻¹ = (r : K) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  refine ⟨r, ?_, fun h => hr (Subtype.ext h), ?_⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact hc.zpow_left n
  · exact elemPow_eq_one_of_isElementaryAbelian (r : K) r.property

/-- The order-1152 recognition statement with quaternion factors in the
ambient group. No weak-closure or normalizer two-group assumption is used. -/
public theorem QuaternionIndependentCubics.exists_fixed_cubic_of_order_1152
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (hG : Nat.card G = 1152)
    (hQ : Nat.card Q = 32) (hself : centralizer (Q : Set G) ≤ Q)
    (B C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (actors : QuaternionIndependentCubics B C)
    (hjoin : B ⊔ C = Q) (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (hVQ : Nat.card (V ⊓ Q : Subgroup G) = 8) :
    ∃ r : G ⧸ Q, r ∈ centralizer (V.map (QuotientGroup.mk' Q) : Set (G ⧸ Q)) ∧
      r ≠ 1 ∧ r ^ 3 = 1 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f := QuotientGroup.mk' Q
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective Q
  have hker : f.ker = Q := QuotientGroup.ker_mk' Q
  obtain ⟨s, hsV, hsQ⟩ : ∃ s : G, s ∈ V ∧ s ∉ Q := by
    by_contra hn
    have hle : V ≤ Q := by
      intro s hs
      by_contra hsQ
      exact hn ⟨s, hs, hsQ⟩
    rw [inf_eq_left.mpr hle, hV] at hVQ
    omega
  have hswap := quaternion_factors_swapped_of_fixed_elementary_eight B C (V ⊓ Q)
    hB hC hinter hcomm (by rwa [hjoin]) (by rwa [hjoin])
    (by rw [hjoin]; exact inf_le_right) hVQ
    (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu.1) s
    (by rw [hjoin, Q.normalizer_eq_top]; trivial) (by rwa [hjoin]) (by
      intro u hu
      exact congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨s, hsV⟩ : V) ⟨u, hu.1⟩))
  let A := actors.A
  have hA : Nat.card A = 9 := actors.card
  have hactors : actors.A = A := rfl
  let E := A.map f
  have hinj : Function.Injective (f.comp A.subtype) :=
    injective_nine_restriction_of_kernel_thirty_two A hA f (by rwa [hker])
  have hrange : (f.comp A.subtype).range = E := by
    rw [MonoidHom.range_comp, A.range_subtype]
  have hE : Nat.card E = 9 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hA]
  have hAe : IsElementaryAbelian 3 A := hactors ▸ actors.elementary
  let : IsElementaryAbelian 3 A := hAe
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map f
  let N := normalizer (B : Set G)
  have hN : N.index = 2 := quaternion_factor_normalizer_index_two_of_swap
    B C hB hC hinter hcomm (by rw [hjoin, Q.normalizer_eq_top]) s hswap.1 hswap.2
  have hQN : Q ≤ N := by
    rw [← hjoin]
    apply sup_le Subgroup.le_normalizer
    apply le_trans ?_ (centralizer_le_normalizer _)
    exact fun c hc b hb => hcomm b hb c hc
  have hNimage : (N.map f).index = 2 := by
    rw [N.index_map_eq hf (by rwa [hker]), hN]
  have hEN : E ≤ N.map f := map_mono (hactors ▸ actors.normalizes_left)
  have hK : Nat.card (G ⧸ Q) = 36 := by
    have hc := card_eq_card_quotient_mul_card_subgroup Q
    rw [hG, hQ] at hc
    omega
  let : E.Normal := normal_nine_of_le_index_two_in_order_thirty_six hK E (N.map f) hE hNimage hEN
  have hnot : ∃ a : E, f s * a * (f s)⁻¹ ≠ (a : G ⧸ Q)⁻¹ := by
    obtain ⟨a, ha⟩ := actors.not_inversion_of_factor_swap hB hcomm f
      (hker.trans hjoin.symm) s hswap.2
    have haA : (a : G) ∈ A := hactors ▸ a.property
    exact ⟨⟨f a, mem_map_of_mem f haA⟩, ha⟩
  have hfs : f s ≠ 1 := by
    intro hh
    exact hsQ (hker ▸ (show s ∈ f.ker from hh))
  have hVimage : V.map f = zpowers (f s) := image_eq_zpowers_of_card_two V f
    (card_image_two_of_sixteen_inf_kernel_eight V f hV (by rwa [hker])) s hsV hfs
  have hs2 : (f s) ^ 2 = 1 := by
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian s hsV, map_one]
  rw [hVimage]
  exact fixed_cubic_of_normal_elementary_noninversion E (f s) hs2 hnot

end Subgroup
