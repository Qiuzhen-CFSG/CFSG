module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.NormalizerProduct.InnerCorrection
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.PGroup

/-!
# Residual containment and the central involution error in a quaternion lift

If the marked two-perfect subgroup generates U/Z(U) by commutators, the
Frattini property of the quaternion central product gives U ≤ O²(H).

For the lifting problem put C = C_H(U). Once C centralizes the selected
involution a, a lift whose action on U commutes with a has error [c,a]
in Z(C), of order at most two. Thus centralizing these central involutions
suffices to remove the error of a cubic lift. Centralizing all of C is
unnecessary for this argument. The inner correction and odd-order lift
retain the actual quotient map H → H/Q and the embedded quaternion factors.

The central-involution control is an explicit additional premise, not a
consequence asserted here. The order-4608 diagnostic described by the
Chapter 14 consumer violates it. In particular the already proved fact
C_H(U) ≤ C_H(A) alone does not supply this premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007, and the quotient-generation input from 12.8.5(1).
This module gives conditional structural deductions, not the source theorem.
-/

open Subgroup
open scoped commutatorElement
namespace Subgroup.QuaternionSourceControl
variable {H : Type*} [Group H]

/-- If a centralizes a normal C, any displacement [c,a] lying in C is a
central involution of C. -/
public theorem central_error (C : Subgroup H) [C.Normal] (a c : H)
    (ha : a ^ 2 = 1) (haC : a ∈ centralizer (C : Set H))
    (he : ⁅c, a⁆ ∈ C) :
    ⁅c, a⁆ ∈ centralizer (C : Set H) ∧ ⁅c, a⁆ ^ 2 = 1 := by
  have hzD : ⁅c, a⁆ ∈ centralizer (C : Set H) :=
    commutator_le_right ⊤ (centralizer (C : Set H))
      (commutator_mem_commutator (mem_top c) haC)
  refine ⟨hzD, ?_⟩
  have hza : Commute ⁅c, a⁆ a := haC _ he
  have hconj : (c * a * c⁻¹) ^ 2 = 1 := by
    change (MulAut.conj c a) ^ 2 = 1
    rw [← map_pow, ha, map_one]
  calc
    ⁅c, a⁆ ^ 2 = ⁅c, a⁆ ^ 2 * a ^ 2 := by rw [ha, mul_one]
    _ = (⁅c, a⁆ * a) ^ 2 := (hza.mul_pow 2).symm
    _ = 1 := by simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hconj

/-- A cubic with displacement in C commutes with a if it fixes the central
involutions of C. No bound on the rest of C is required. -/
public theorem commute_of_central_involutions (C : Subgroup H) [C.Normal] (a c : H)
    (ha : a ^ 2 = 1) (hc : c ^ 3 = 1)
    (haC : a ∈ centralizer (C : Set H)) (he : ⁅c, a⁆ ∈ C)
    (hcontrol : ∀ z ∈ C, z ∈ centralizer (C : Set H) → z ^ 2 = 1 → Commute c z) :
    Commute c a := by
  obtain ⟨hzD, hz2⟩ := central_error C a c ha haC he
  let z := ⁅c, a⁆
  have hzc : Commute z c := (hcontrol z he hzD hz2).symm
  have hzc' : Commute z (a * c * a⁻¹) := by
    have heq : a * c * a⁻¹ = z⁻¹ * c := by dsimp [z]; simp only [commutatorElement_def]; group
    rw [heq]
    exact (Commute.refl z).inv_right.mul_right hzc
  have hz3 : z ^ 3 = 1 := by
    have heq : c = z * (a * c * a⁻¹) := by dsimp [z]; simp only [commutatorElement_def]; group
    have hp : (a * c * a⁻¹) ^ 3 = 1 := by
      change (MulAut.conj a c) ^ 3 = 1
      rw [← map_pow, hc, map_one]
    have hh := congrArg (fun x : H => x ^ 3) heq
    rw [hc, hzc'.mul_pow, hp, mul_one] at hh
    exact hh.symm
  have hz1 : z = 1 := by
    change z ^ 2 = 1 at hz2
    rw [show 3 = 2 + 1 from rfl, pow_succ, hz2, one_mul] at hz3
    exact hz3
  exact commutatorElement_eq_one_iff_mul_comm.mp hz1

variable [Finite H]
/-- Quotient commutator generation by a two-perfect subgroup places the
whole quaternion core in the actual two-residual. -/
public theorem core_le_residual (U : Subgroup H) [U.Normal]
    (d : QuaternionCentralProductData U) (R : Subgroup H) (hR : IsPPerfect 2 R)
    (hspan : (⁅U, R⁆.subgroupOf U).map (QuotientGroup.mk' (center U)) = ⊤) :
    U ≤ pResidual 2 H := by
  let : IsExtraspecial 2 U := d.extraspecial
  have hspan' : ⁅U, R⁆.subgroupOf U ⊔ center U = ⊤ := by
    have he := congrArg (fun S : Subgroup (U ⧸ center U) =>
      S.comap (QuotientGroup.mk' (center U))) hspan
    simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using he
  have hfull : ⁅U, R⁆.subgroupOf U = ⊤ := by
    apply frattini_nongenerating
    rwa [IsExtraspecial.frattini_eq_center_two]
  have hUK : U ≤ ⁅U, R⁆ := by
    intro u hu
    have hh : (⟨u, hu⟩ : U) ∈ ⁅U, R⁆.subgroupOf U := hfull ▸ mem_top _
    exact hh
  exact hUK.trans ((commutator_mono le_rfl (le_pResidual_of_isPPerfect R hR)).trans
    (commutator_le_right U (pResidual 2 H)))
end Subgroup.QuaternionSourceControl

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

/-- A cubic in the quotient centralizer lifts through the extra kernel
when a fixes that kernel and K fixes its central involutions. This retains
the literal quotient, and does not assume U = Q. -/
public theorem cubic_centralizer_lift_of_central_involutions
    (Q : Subgroup H) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hker : ((quotientAut (center U)).comp
      (MulAut.conjNormal : H →* MulAut U)).ker = Q)
    (K : Subgroup H) (hUK : U ≤ K)
    (a : H) (ha : a ^ 2 = 1)
    (hfix : centralizer (U : Set H) ≤ centralizer ({a} : Set H))
    (hcontrol : ∀ c ∈ K, ∀ z ∈ centralizer (U : Set H),
      z ∈ centralizer (centralizer (U : Set H) : Set H) → z ^ 2 = 1 → Commute c z)
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
  have haC : a ∈ centralizer (centralizer (U : Set H) : Set H) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hfix hx)
  have hca := QuaternionSourceControl.commute_of_central_involutions
    (centralizer (U : Set H)) a c ha hc3 haC hzC (hcontrol c hcK)
  exact ⟨c, hcK, hc3, hca, hcπ⟩
end Subgroup.QuaternionCentralProductData
