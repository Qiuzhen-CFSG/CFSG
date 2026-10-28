module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers

/-!
# The two involution classes in the elementary normalizer

The A6 quotient has one involution class. Its conjugators lift to N(E),
and a coordinate calculation conjugates every involution in Ea to a by E.
Thus every involution outside E is conjugate to a in the actual normalizer.
Transitivity on E transports C(z) into N(E), reducing centralizer closure
to the full ambient centralizer of a. No complement is assumed.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 7, p.7, and Section 5, pp.9–10.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy

private theorem alternating_six_involutions_conjugate
    (s t : alternatingGroup (Fin 6)) (hs : orderOf s = 2) (ht : orderOf t = 2) :
    IsConj s t := by
  have hsct := alternatingGroup.involution_cycleType_of_degree_le_six (by rfl) s hs
  have htct := alternatingGroup.involution_cycleType_of_degree_le_six (by rfl) t ht
  apply alternatingGroup.isConj_of
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr (hsct.trans htct.symm))
  have hc := (s : Equiv.Perm (Fin 6)).sum_cycleType
  rw [hsct] at hc
  norm_num at hc
  simpa only [Fintype.card_fin, hc] using (show 4 + 2 ≤ 6 by omega)

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

private theorem involutions_in_Ea : ∀ x : TwistedModel,
    x.right = a.right → x ^ 2 = 1 →
    ∃ v : BinaryFour, SemidirectProduct.inl v * x * (SemidirectProduct.inl v)⁻¹ = a := by
  decide +kernel

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

private theorem into_mem_normalizerE (x : TwistedModel) :
    into D k x ∈ normalizer (E D k : Set G) :=
  centralizer_le_normalizer_E D k (k x).property

private theorem into_mem_E_iff (x : TwistedModel) :
    into D k x ∈ E D k ↔ x.right = 1 := by
  rw [← modelE_map D k, mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    have hxy : y = x := into_injective D k he
    subst y
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Quotient fusion lifts to actual fusion of all involutions outside E. -/
public theorem normalizer_involution_outside_E_conjugate_a
    (hE : ENormalizerAction D k) (t : G)
    (htN : t ∈ normalizer (E D k : Set G)) (ht : orderOf t = 2)
    (htE : t ∉ E D k) :
    ∃ n : normalizer (E D k : Set G), (n : G) * t * (n : G)⁻¹ = into D k a := by
  let N := normalizer (E D k : Set G)
  let B := (E D k).subgroupOf N
  let tN : N := ⟨t, htN⟩
  let aN : N := ⟨into D k a, into_mem_normalizerE D k a⟩
  have ht2 : tN ^ 2 = 1 := by
    apply Subtype.ext
    exact ht ▸ pow_orderOf_eq_one t
  have ha2 : aN ^ 2 = 1 := by
    apply Subtype.ext
    change (into D k a) ^ 2 = 1
    rw [← map_pow, show a ^ 2 = 1 from by decide +kernel, map_one]
  have haB : aN ∉ B := by
    intro h
    have h' := (into_mem_E_iff D k a).mp h
    have hn : a.right ≠ 1 := by decide +kernel
    exact hn h'
  obtain ⟨e⟩ := hE.quotient
  let q : N →* N ⧸ B := QuotientGroup.mk' B
  have hqt : q tN ≠ 1 := fun h => htE ((QuotientGroup.eq_one_iff tN).mp h)
  have hqa : q aN ≠ 1 := fun h => haB ((QuotientGroup.eq_one_iff aN).mp h)
  have hc : IsConj (e (q tN)) (e (q aN)) :=
    alternating_six_involutions_conjugate _ _
      (orderOf_eq_prime
        (by rw [← map_pow, ← map_pow, ht2, map_one, map_one])
        (fun h => hqt (e.injective (h.trans e.map_one.symm))))
      (orderOf_eq_prime
        (by rw [← map_pow, ← map_pow, ha2, map_one, map_one])
        (fun h => hqa (e.injective (h.trans e.map_one.symm))))
  have hcq : IsConj (q tN) (q aN) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      e.symm.toMonoidHom.map_isConj hc
  obtain ⟨u, hu⟩ := isConj_iff.mp hcq
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective u
  have hgq : q (g * tN * g⁻¹) = q aN := by
    simpa only [map_mul, map_inv, show q g = u from hg] using hu
  have hvB : (g * tN * g⁻¹) / aN ∈ B := QuotientGroup.eq_iff_div_mem.mp hgq
  have hvE : ((g : G) * t * (g : G)⁻¹) / into D k a ∈ E D k := hvB
  rw [← modelE_map D k] at hvE
  obtain ⟨v, hv, he⟩ := hvE
  let x := v * a
  have hxg : into D k x = (g : G) * t * (g : G)⁻¹ := by
    simp only [x, map_mul, he, div_mul_cancel]
  have hxr : x.right = a.right := by
    change v.right * a.right = a.right
    change v.right = 1 at hv
    rw [hv, one_mul]
  have hx2 : x ^ 2 = 1 := by
    apply into_injective D k
    rw [map_pow, hxg, map_one]
    calc
      ((g : G) * t * (g : G)⁻¹) ^ 2 =
          (g : G) * t ^ 2 * (g : G)⁻¹ :=
            (map_pow (MulAut.conj (g : G)) _ _).symm
      _ = 1 := by rw [show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t]; group
  obtain ⟨v', hv'⟩ := involutions_in_Ea x hxr hx2
  refine ⟨⟨into D k (SemidirectProduct.inl v') * (g : G),
    N.mul_mem (into_mem_normalizerE D k _) g.property⟩, ?_⟩
  change (into D k (SemidirectProduct.inl v') * (g : G)) * t *
    (into D k (SemidirectProduct.inl v') * (g : G))⁻¹ = into D k a
  calc
    _ = into D k (SemidirectProduct.inl v') * into D k x *
        (into D k (SemidirectProduct.inl v'))⁻¹ := by rw [hxg]; group
    _ = into D k a := by simpa only [map_mul, map_inv] using congrArg (into D k) hv'

private theorem centralizer_le_of_conjugate (N : Subgroup G) {s t : G}
    (n : N) (hn : (n : G) * s * (n : G)⁻¹ = t)
    (ht : centralizer ({t} : Set G) ≤ N) : centralizer ({s} : Set G) ≤ N := by
  intro x hx
  have hxc : (n : G) * x * (n : G)⁻¹ ∈ centralizer ({t} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hn]
    simpa only [map_mul, MulAut.conj_apply] using congrArg (MulAut.conj (n : G))
      (mem_centralizer_singleton_iff.mp hx)
  have hmem := N.mul_mem (N.mul_mem (N.inv_mem n.property) (ht hxc)) n.property
  simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hmem

/-- The actor d is in the same actual normalizer class as a. -/
public theorem normalizer_actor_d_conjugate_a (hE : ENormalizerAction D k) :
    ∃ n : normalizer (E D k : Set G),
      (n : G) * into D k d * (n : G)⁻¹ = into D k a := by
  apply normalizer_involution_outside_E_conjugate_a D k hE _
    (into_mem_normalizerE D k d)
  · rw [orderOf_injective (into D k) (into_injective D k)]
    exact actor_orders.2.2.2
  · rw [into_mem_E_iff D k]
    decide +kernel

/-- Contrary actor nonfusion prevents a conjugate of z in N(E) from leaving E. -/
public theorem marked_conjugate_mem_E (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) {t : G}
    (htN : t ∈ normalizer (E D k : Set G)) (hzt : IsConj D.z t) : t ∈ E D k := by
  by_contra htE
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzt
    rw [← hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq, D.z_order]
  obtain ⟨n, hna⟩ := normalizer_involution_outside_E_conjugate_a D k hE t htN ht htE
  obtain ⟨m, hma⟩ := normalizer_actor_d_conjugate_a D k hE
  exact hn (hzt.trans ((isConj_iff.mpr ⟨(n : G), hna⟩).trans
    (isConj_iff.mpr ⟨(m : G), hma⟩).symm))

variable [Finite G]

/-- All nonidentity elements of E have their full centralizer in N(E). -/
public theorem E_element_centralizer_le_normalizer
    (hE : ENormalizerAction D k) (t : G) (htE : t ∈ E D k) (ht : t ≠ 1) :
    centralizer ({t} : Set G) ≤ normalizer (E D k : Set G) := by
  obtain ⟨n, hn⟩ := hE.fusion ⟨t, htE⟩ (eNormalizerPoint D k)
    (fun h => ht (congrArg Subtype.val h)) (eNormalizerPoint_ne_one D k)
  exact centralizer_le_of_conjugate _ n hn (centralizer_le_normalizer_E D k)

/-- Centralizer closure of N(E) reduces to the single source actor a. -/
public theorem E_centralizer_closure_of_actor_a
    (hE : ENormalizerAction D k)
    (ha : centralizer ({into D k a} : Set G) ≤ normalizer (E D k : Set G)) :
    ∀ t ∈ normalizer (E D k : Set G), orderOf t = 2 →
      centralizer ({t} : Set G) ≤ normalizer (E D k : Set G) := by
  intro t htN ht
  by_cases htE : t ∈ E D k
  · exact E_element_centralizer_le_normalizer D k hE t htE
      (by intro h; simp [h] at ht)
  · obtain ⟨n, hn⟩ := normalizer_involution_outside_E_conjugate_a D k hE t htN ht htE
    exact centralizer_le_of_conjugate _ n hn ha

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
