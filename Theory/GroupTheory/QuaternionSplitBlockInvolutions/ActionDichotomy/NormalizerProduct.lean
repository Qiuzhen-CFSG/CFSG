module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.NormalizerProduct.InnerCorrection
public import Mathlib.GroupTheory.PGroup

/-!
# Lifting the swapping-branch normalizer product

An element of K whose cubic image centralizes a* first receives an inner
correction in U, making its action on U commute with a. A suitable fourth
power has cube one and the same quotient image. If K centralizes C_H(U),
its commutator with a is central relative to this lift; it has both odd
order and two-power order, and therefore vanishes. This supplies an actual
centralizing cubic, not just an automorphism of U.

The final theorem combines this lift with a decomposition inside K* and
normalization by a supplement T. Normality of the marked R* converts the
resulting join into the requested literal set product. Neither U = Q nor
self-centralization of U is used.

The product theorem only requires this centralizer control on the preimage
in K of C_{K*}(a*). It is an explicit additional input. The source assembly
must derive adequate control from the genuine block and ambient hypotheses;
the reduced local action assumptions do not imply it. In particular
C_H(U) ≤ C_H(A) alone is insufficient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the quaternion
action step in the proof of 14.4.4, printed p.1007. This module proves the
conditional lifting step, not the full source assertion.
-/

open Subgroup
open scoped Pointwise

namespace Subgroup.QuaternionCentralProductData
open scoped commutatorElement
variable {H : Type*} [Group H] [Finite H] (U : Subgroup H) [U.Normal]
    (d : QuaternionCentralProductData U)

omit [Finite H] in
private theorem conjNormal_eq_one_iff (x : H) :
    (MulAut.conjNormal x : MulAut U) = 1 ↔ x ∈ centralizer (U : Set H) := by
  constructor
  · intro hx y hy
    have he := congrArg Subtype.val (DFunLike.congr_fun hx (⟨y, hy⟩ : U))
    change x * y * x⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change x * (y : H) * x⁻¹ = y
    rw [← hx y y.property, mul_inv_cancel_right]

/-- A cubic in the quotient centralizer lifts to an actual cubic centralizing
a, provided K centralizes the extra kernel C_H(U). -/
public theorem cubic_centralizer_lift
    (Q : Subgroup H) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hker : ((quotientAut (center U)).comp
      (MulAut.conjNormal : H →* MulAut U)).ker = Q)
    (K : Subgroup H) (hUK : U ≤ K)
    (hKC : K ≤ centralizer (centralizer (U : Set H) : Set H))
    (a : H) (ha : a ^ 2 = 1)
    (hswap : d.left.map (MulAut.conjNormal a).toMonoidHom = d.right)
    (k : H) (hk : k ∈ K)
    (hk3 : (QuotientGroup.mk' Q k) ^ 3 = 1)
    (hka : Commute (QuotientGroup.mk' Q k) (QuotientGroup.mk' Q a)) :
    ∃ c ∈ K, c ^ 3 = 1 ∧ Commute c a ∧
      QuotientGroup.mk' Q c = QuotientGroup.mk' Q k := by
  let f : H →* MulAut U := MulAut.conjNormal
  let σ := (quotientAut (center U)).comp f
  let π := QuotientGroup.mk' Q
  have heq (x y : H) : σ x = σ y ↔ π x = π y := by
    rw [σ.eq_iff, π.eq_iff, hker, QuotientGroup.ker_mk']
  have hUQ : U ≤ Q := by
    intro u hu
    rw [← hker]
    change quotientAut (center U) (f u) = 1
    apply (d.quotientAut_eq_one_iff_inner _).mpr
    exact ⟨⟨u, hu⟩, MulEquiv.ext (fun _ => rfl)⟩
  let α := f a
  let β := f k * α * (f k)⁻¹
  have hα : α ^ 2 = 1 := by dsimp [α]; rw [← map_pow, ha, map_one]
  have hβ : β ^ 2 = 1 := by
    dsimp [β]
    calc
      _ = f k * α ^ 2 * (f k)⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hα]; group
  have hquot : quotientAut (center U) β = quotientAut (center U) α := by
    have hs : σ (k * a * k⁻¹) = σ a := (heq _ _).mpr (by
      rw [map_mul, map_mul, map_inv, hka.eq, mul_inv_cancel_right])
    simpa only [σ, β, α, MonoidHom.comp_apply, map_mul, map_inv] using hs
  obtain ⟨u, hu⟩ := d.swap_inner_correction α β hα hβ hswap hquot
  let b : H := (u : H) * k
  have hbK : b ∈ K := K.mul_mem (hUK u.property) hk
  have hbπ : π b = π k := by
    change π ((u : H) * k) = _
    rw [map_mul, show π u = 1 from (QuotientGroup.eq_one_iff _).mpr (hUQ u.property), one_mul]
  have hbcomm : Commute (f b) α := by
    apply mul_inv_eq_iff_eq_mul.mp
    dsimp [b]
    rw [map_mul, show f (u : H) = MulAut.conj u from MulAut.conjNormal_val]
    calc
      _ = MulAut.conj u * β * (MulAut.conj u)⁻¹ := by dsimp [β]; group
      _ = α := hu
  have hb3 : b ^ 3 ∈ Q := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (b ^ 3) = 1
    rw [map_pow, hbπ]
    exact hk3
  obtain ⟨n, hn⟩ := hQ.exists_pow_pow_eq_one (⟨b ^ 3, hb3⟩ : Q)
  have hn' : (b ^ 3) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  let c := b ^ (4 ^ n)
  have hcK : c ∈ K := K.pow_mem hbK _
  have hc3 : c ^ 3 = 1 := by
    calc
      c ^ 3 = ((b ^ 3) ^ (2 ^ n)) ^ (2 ^ n) := by
        simp only [c, ← pow_mul]
        congr 1
        rw [show 4 = 2 * 2 from rfl, mul_pow]
        ring
      _ = 1 := by rw [hn', one_pow]
  have hcπ : π c = π k := by
    rw [map_pow, hbπ]
    have hp : (π k) ^ 4 = π k := by rw [show 4 = 3 + 1 from rfl, pow_succ, hk3, one_mul]
    have hpower (m : ℕ) : (π k) ^ (4 ^ m) = π k := by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_mul, ih, hp]
    exact hpower n
  have hccomm : Commute (f c) α := by
    change Commute (f (b ^ (4 ^ n))) α
    rw [map_pow]
    exact hbcomm.pow_left _
  let z := ⁅c, a⁆
  have hzC : z ∈ centralizer (U : Set H) := by
    apply (conjNormal_eq_one_iff U z).mp
    change f ⁅c, a⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hccomm.eq
  have hzQ : z ∈ Q := by
    rw [← hker]
    change quotientAut (center U) (f z) = 1
    rw [(conjNormal_eq_one_iff U z).mpr hzC, map_one]
  have hzc : Commute z c := hKC hcK z hzC
  have hzc' : Commute z (a * c * a⁻¹) := by
    have he : a * c * a⁻¹ = z⁻¹ * c := by dsimp [z]; simp only [commutatorElement_def]; group
    rw [he]
    exact (Commute.refl z).inv_right.mul_right hzc
  have hz3 : z ^ 3 = 1 := by
    have he : c = z * (a * c * a⁻¹) := by dsimp [z]; simp only [commutatorElement_def]; group
    have hp : (a * c * a⁻¹) ^ 3 = 1 := by
      change (MulAut.conj a c) ^ 3 = 1
      rw [← map_pow, hc3, map_one]
    have hh := congrArg (fun x : H => x ^ 3) he
    rw [hc3, hzc'.mul_pow, hp, mul_one] at hh
    exact hh.symm
  have hz1 : z = 1 := by
    have ho := hQ.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨z, hzQ⟩ : Q)
    have hd : orderOf (⟨z, hzQ⟩ : Q) ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hz3)
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp (ho.eq_one_of_dvd hd))
  exact ⟨c, hcK, hc3, commutatorElement_eq_one_iff_mul_comm.mp hz1, hcπ⟩
end Subgroup.QuaternionCentralProductData

namespace Subgroup.QuaternionCentralProductData
variable {H : Type*} [Group H] [Finite H] (U : Subgroup H) [U.Normal]
    (d : QuaternionCentralProductData U)

omit [Finite H] in
/-- Centralizing a normalizes the literal subgroup generated by a and [U,a]. -/
public theorem centralizer_le_normalizer_sixteen (a : H) :
    centralizer ({a} : Set H) ≤
      normalizer ((zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup H) : Set H) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq, map_sup, map_commutator, MonoidHom.map_zpowers]
  have hxa : MulAut.conj x a = a := by
    change x * a * x⁻¹ = a
    rw [mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
  have hxU : U.map (MulAut.conj x).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [U.normalizer_eq_top]; trivial)
  change zpowers (MulAut.conj x a) ⊔
    ⁅U.map (MulAut.conj x).toMonoidHom, zpowers (MulAut.conj x a)⁆ = _
  rw [hxa, hxU]

/-- Lift the quotient cubic decomposition to the literal normalizer product.
The extra-centralizer control and the Sylow normalization are explicit inputs;
this conditional theorem does not discharge their source provenance. -/
public theorem normalizer_product_of_centralizer_control
    (Q : Subgroup H) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hker : ((quotientAut (center U)).comp
      (MulAut.conjNormal : H →* MulAut U)).ker = Q)
    (K R T : Subgroup H) (hUK : U ≤ K)
    (a : H) (ha : a ^ 2 = 1)
    (hKC : K ⊓ (centralizer ({QuotientGroup.mk' Q a} : Set (H ⧸ Q))).comap
      (QuotientGroup.mk' Q) ≤ centralizer (centralizer (U : Set H) : Set H))
    (hK : IsElementaryAbelian 3 (K.map (QuotientGroup.mk' Q)))
    (hswap : d.left.map (MulAut.conjNormal a).toMonoidHom = d.right)
    (hT : T ≤ normalizer ((zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup H) : Set H))
    (hKT : K ⊔ T = ⊤)
    (hRn : (R.map (QuotientGroup.mk' Q)).Normal)
    (hcover : (K.map (QuotientGroup.mk' Q) : Set (H ⧸ Q)) ⊆
      ((K.map (QuotientGroup.mk' Q) ⊓
        centralizer ({QuotientGroup.mk' Q a} : Set (H ⧸ Q)) : Subgroup (H ⧸ Q)) :
          Set (H ⧸ Q)) * (R.map (QuotientGroup.mk' Q) : Set (H ⧸ Q))) :
    ((normalizer ((zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup H) : Set H)).map
      (QuotientGroup.mk' Q) : Set (H ⧸ Q)) *
        (R.map (QuotientGroup.mk' Q) : Set (H ⧸ Q)) = Set.univ := by
  let π := QuotientGroup.mk' Q
  let N := normalizer ((zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup H) : Set H)
  let K₀ := K ⊓ (centralizer ({π a} : Set (H ⧸ Q))).comap π
  have hUK₀ : U ≤ K₀ := by
    intro u hu
    refine ⟨hUK hu, ?_⟩
    have huQ : u ∈ Q := by
      rw [← hker]
      change quotientAut (center U) (MulAut.conjNormal u) = 1
      apply (d.quotientAut_eq_one_iff_inner _).mpr
      exact ⟨⟨u, hu⟩, MulEquiv.ext (fun _ => rfl)⟩
    change π u ∈ centralizer ({π a} : Set (H ⧸ Q))
    rw [show π u = 1 from (QuotientGroup.eq_one_iff _).mpr huQ]
    exact (centralizer _).one_mem
  let : IsElementaryAbelian 3 (K.map π) := hK
  have hC : K.map π ⊓ centralizer ({π a} : Set (H ⧸ Q)) ≤ N.map π := by
    rintro x ⟨⟨k, hk, rfl⟩, hc⟩
    obtain ⟨c, _, _, hca, he⟩ := d.cubic_centralizer_lift U Q hQ hker K₀ hUK₀ hKC
      a ha hswap k ⟨hk, hc⟩ (elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem π hk))
        (mem_centralizer_singleton_iff.mp hc)
    exact ⟨c, centralizer_le_normalizer_sixteen U a
      (mem_centralizer_singleton_iff.mpr hca), he⟩
  have hKle : K.map π ≤ N.map π ⊔ R.map π := by
    intro x hx
    obtain ⟨c, hc, r, hr, rfl⟩ := hcover hx
    exact (N.map π ⊔ R.map π).mul_mem (mem_sup_left (hC hc)) (mem_sup_right hr)
  have hjoin : N.map π ⊔ R.map π = ⊤ := by
    apply top_unique
    have hh : (K ⊔ T).map π ≤ N.map π ⊔ R.map π := by
      rw [map_sup]
      exact sup_le hKle ((map_mono hT).trans le_sup_left)
    rw [hKT, map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)] at hh
    exact hh
  let := hRn
  rw [← coe_mul_of_left_le_normalizer_right (N.map π) (R.map π)
    (by rw [normalizer_eq_top]; exact le_top), hjoin]
  rfl
end Subgroup.QuaternionCentralProductData
