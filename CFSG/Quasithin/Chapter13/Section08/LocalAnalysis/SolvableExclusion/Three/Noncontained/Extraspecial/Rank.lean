module

public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.CubicInverter
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ExtraspecialExtensions
public import Theory.SpecificGroups.HeisenbergPrime.Recognition

/-!
# Constructing elementary subgroups in the extraspecial branch

For the literal extraspecial group P of order 27 and exponent three, the
cubic residual supplies an order-three actor and a commuting inverter on
P/Z(P). The fixed-plane theorem and the independent actor construct an
elementary subgroup of order 27 in the prescribed join. The alternate
inner-action case is handled by correcting the actor by an element of P;
the correction still has order three because P has exponent three.

This is the rank construction for 13.8.13, not the construction of its
local residual or action alternative. Those inputs remain explicit.

Source: Aschbacher–Smith, proof of 13.8.13, printed p.951 (PDF p.968),
and A.1.33(1), printed p.29. The cubic-inverter argument is the same
intrinsic argument used in 15.4.10, printed p.1159.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Extraspecial

variable {Q : Type*} [Group Q] [Finite Q]

private theorem quotient_action_kernel_congr {V : Type*} [Group V]
    (A B : Subgroup V) [A.Characteristic] [B.Characteristic] (h : A = B) :
    (quotientAut A).ker = (quotientAut B).ker := by
  subst B
  rfl

private theorem heisenberg_model (P : Subgroup Q) [IsExtraspecial 3 P]
    (hc : Nat.card P = 27) (hexp : ∀ x : P, x ^ 3 = 1) :
    Nonempty (P ≃* HeisenbergPrime 3) := by
  apply HeisenbergPrime.nonempty_mulEquiv_of_card_prime_cube hc hexp
    (IsExtraspecial.commutator_eq_center (p := 3)).le
  intro hn
  have hh : center P = ⊤ := center_eq_top_iff.mpr hn
  have hz := IsExtraspecial.center_order_p 3 P
  rw [hh, Nat.card_congr (topEquiv : (⊤ : Subgroup P) ≃* P).toEquiv, hc] at hz
  norm_num at hz

private theorem fixed_join_in (P J E : Subgroup Q) (hPJ : P ≤ J)
    (hEP : E ≤ P) [IsElementaryAbelian 3 E]
    (hc : Nat.card E = 9) (x : Q) (hxJ : x ∈ J)
    (hx : orderOf x = 3) (hxP : x ∉ P)
    (hfix : E ≤ centralizer ({x} : Set Q)) :
    ∃ A : Subgroup Q, A ≤ J ∧ IsElementaryAbelian 3 A ∧ Nat.card A = 27 := by
  have hxE : x ∉ E := fun h => hxP (hEP h)
  obtain ⟨ha, hc⟩ := IsElementaryAbelian.fixed_join_card (p := 3) (n := 2)
    E x hx (E.disjoint_zpowers_of_prime_order_not_mem x hx hxE) hfix hc
  exact ⟨E ⊔ zpowers x, sup_le (hEP.trans hPJ) (zpowers_le.mpr hxJ), ha, hc⟩

/-- A commuting inverter and an actual cubic actor construct an elementary
subgroup of order 27 inside the specified overgroup of P. -/
theorem elementary_of_inverter (P J : Subgroup Q) [P.Normal]
    [IsExtraspecial 3 P] (hc : Nat.card P = 27) (hexp : ∀ x : P, x ^ 3 = 1)
    (hPJ : P ≤ J) (t x : Q) (hxJ : x ∈ J)
    (ht : ∀ v : P ⧸ center P,
      quotientAut (center P) (MulAut.conjNormal t) v = v⁻¹)
    (hx : orderOf x = 3) (hxt : x ∈ centralizer ({t} : Set Q))
    (hxV : quotientAut (center P) (MulAut.conjNormal x) ≠ 1) :
    ∃ A : Subgroup Q, A ≤ J ∧ IsElementaryAbelian 3 A ∧ Nat.card A = 27 := by
  obtain ⟨e⟩ := heisenberg_model P hc hexp
  obtain ⟨E, hEP, hfix, hE, hcard⟩ :=
    ChapterA.RankActions.exists_extraspecial_fixed_plane_of_inverter P e
      (by decide : 3 ≠ 2) t x ht hx hxt hxV
  let := hE
  have hxP : x ∉ P := by
    intro hxP
    apply hxV
    let : IsElementaryAbelian 3 (P ⧸ center P) :=
      IsExtraspecial.quotient_elementary_abelian 3 P
    let y : P := ⟨x, hxP⟩
    have hconj : (MulAut.conjNormal x : MulAut P) = MulAut.conj y :=
      MulAut.conjNormal_val (h := y)
    ext v
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (center P) v
    rw [quotientAut_apply_mk, hconj, MulAut.conj_apply, map_mul, map_mul, map_inv]
    change _ = QuotientGroup.mk' (center P) z
    rw [mul_comm (QuotientGroup.mk' (center P) y), mul_assoc, mul_inv_cancel, mul_one]
  exact fixed_join_in P J E hPJ hEP hcard x hxJ hx hxP hfix

/-- An outside cubic actor trivial on P/Z(P) can be corrected by an element
of P to centralize P, preserving its order and giving an elementary 27. -/
theorem elementary_of_inner_actor (P J : Subgroup Q) [P.Normal]
    [IsExtraspecial 3 P] (hc : Nat.card P = 27) (hexp : ∀ x : P, x ^ 3 = 1)
    (hPJ : P ≤ J) (x : Q) (hxJ : x ∈ J) (hx : orderOf x = 3)
    (hxP : x ∉ P) (hxV : quotientAut (center P) (MulAut.conjNormal x) = 1) :
    ∃ A : Subgroup Q, A ≤ J ∧ IsElementaryAbelian 3 A ∧ Nat.card A = 27 := by
  have hi : (MulAut.conjNormal x : MulAut P) ∈ (MulAut.conj : P →* MulAut P).range := by
    rw [← IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 3)]
    exact hxV
  obtain ⟨y, hy⟩ := hi
  have hyconj : (MulAut.conjNormal (y : Q) : MulAut P) = MulAut.conjNormal x := by
    rw [MulAut.conjNormal_val]
    exact hy
  let z := (y : Q)⁻¹ * x
  have hzact : (MulAut.conjNormal z : MulAut P) = 1 := by
    change MulAut.conjNormal ((y : Q)⁻¹ * x) = 1
    rw [map_mul, map_inv, hyconj, inv_mul_cancel]
  have hzC : z ∈ centralizer (P : Set Q) := by
    intro w hw
    have he := congrArg Subtype.val (DFunLike.congr_fun hzact (⟨w, hw⟩ : P))
    rw [MulAut.conjNormal_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hxy : Commute (y : Q) x := by
    have he := congrArg Subtype.val (DFunLike.congr_fun hy y)
    change (y : Q) * (y : Q) * (y : Q)⁻¹ = x * (y : Q) * x⁻¹ at he
    rw [mul_inv_cancel_right] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  have hz3 : z ^ 3 = 1 := by
    rw [show z = (y : Q)⁻¹ * x from rfl, hxy.inv_left.mul_pow,
      inv_pow, show (y : Q) ^ 3 = 1 from congrArg Subtype.val (hexp y),
      show x ^ 3 = 1 from hx ▸ pow_orderOf_eq_one x, inv_one, one_mul]
  have hzP : z ∉ P := by
    intro hz
    have hh := P.mul_mem y.property hz
    apply hxP
    simpa only [z, mul_inv_cancel_left] using hh
  have hz : orderOf z = 3 := orderOf_eq_prime hz3 (fun h => hzP (h ▸ P.one_mem))
  obtain ⟨e⟩ := heisenberg_model P hc hexp
  obtain ⟨E, hE, hcard⟩ := HeisenbergPrime.exists_elementary_plane (by decide : 3 ≠ 2)
  let := hE
  let f := P.subtype.comp e.symm.toMonoidHom
  let B := E.map f
  have hf : Function.Injective f := P.subtype_injective.comp e.symm.injective
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.map f
  have hBP : B ≤ P := by
    rintro w ⟨v, hv, rfl⟩
    exact (e.symm v).property
  have hBc : Nat.card B = 9 :=
    (Nat.card_congr (E.equivMapOfInjective f hf).toEquiv).symm.trans hcard
  exact fixed_join_in P J B hPJ hBP hBc z
    (J.mul_mem (J.inv_mem (hPJ y.property)) hxJ) hz hzP
    (fun w hw => mem_centralizer_singleton_iff.mpr (hzC w (hBP hw)))

/-- Construct the inverter and cubic actor in the original residual, then
construct the elementary 27 inside the subgroup containing its image and P. -/
theorem elementary_of_cubic_residual (P J : Subgroup Q) [P.Normal]
    [IsExtraspecial 3 P] (hc : Nat.card P = 27) (hexp : ∀ x : P, x ^ 3 = 1)
    (hPJ : P ≤ J) {X : Type*} [Group X] [Finite X]
    (hX : IsPPerfect 2 X) (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (f : X →* Q) (hfJ : ∀ x, f x ∈ J)
    (hne : (pCore 2 X).map ((MulAut.conjNormal : Q →* MulAut P).comp f) ≠ ⊥) :
    ∃ A : Subgroup Q, A ≤ J ∧ IsElementaryAbelian 3 A ∧ Nat.card A = 27 := by
  let a := (MulAut.conjNormal : Q →* MulAut P).comp f
  let b := (quotientAut (center P)).comp a
  let : IsElementaryAbelian 3 (P ⧸ center P) :=
    IsExtraspecial.quotient_elementary_abelian 3 P
  have hcard : Nat.card (P ⧸ center P) = 9 := by
    have hh := (center P).index_mul_card
    change Nat.card (P ⧸ center P) * Nat.card (center P) = Nat.card P at hh
    rw [IsExtraspecial.center_order_p 3 P, hc] at hh
    omega
  have hb : (pCore 2 X).map b ≠ ⊥ := by
    have hh := Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.twoCore_frattini_image_ne_bot
      (by decide : 3 ≠ 2) (IsExtraspecial.isPGroup 3 P) a hne
    have hk := quotient_action_kernel_congr _ _
      (IsExtraspecial.frattini_eq_center (p := 3) (P := P))
    intro hb
    apply hh
    rw [Subgroup.map_eq_bot_iff, ← MonoidHom.comap_ker, hk]
    exact (Subgroup.map_eq_bot_iff _).mp hb
  obtain ⟨x, t, hx, hxV, htx, ht⟩ :=
    Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.exists_commuting_inverter hcard hX hX3 b hb
  have hfx : orderOf (f x) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (hx ▸ orderOf_map_dvd f x) with h | h
    · exfalso
      apply hxV
      change quotientAut (center P) (MulAut.conjNormal (f x)) = 1
      rw [orderOf_eq_one_iff.mp h, map_one, map_one]
    · exact h
  exact elementary_of_inverter P J hc hexp hPJ (f t) (f x) (hfJ x) ht hfx
    (mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul] using (congrArg f htx).symm)) hxV

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Extraspecial

end
