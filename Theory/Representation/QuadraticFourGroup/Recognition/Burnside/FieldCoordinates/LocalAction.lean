module

public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside.Action
public import Theory.GroupTheory.InvolutionOddProduct
public import Mathlib.GroupTheory.FixedPointFree

/-!
# The two-point stabilizer in Burnside's Sylow action

Under the involution-or-odd-order condition, two involutions in different
Sylow subgroups have odd-order product and hence are conjugate. A third
involution connects two in the same Sylow subgroup. Burnside fusion and
regularity of the root group then show that the two-point stabilizer acts
regularly on the nonidentity elements of that root group and on the remaining
Sylow subgroups.

An element swapping the marked points has even order, so is an involution.
It induces a fixed-point-free involution on their stabilizer, which is
therefore abelian and is inverted by the swap. These are actual subgroups
and actions; no field or projective-line coordinates are assumed.

Source: W. Burnside, *On a Class of Groups of Finite Order* (1900),
pp. 271–272 and 274–276, `refs/original/burnside-1900.pdf`. The prior
`Action` module supplies the Sylow count and regular root action.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.InvolutionOddSpectrum
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem involution_mem_sylow {u : G} (hu : orderOf u = 2) :
    ∃ P : Sylow 2 G, u ∈ P := by
  have hp : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1) (by simpa using (Nat.card_zpowers u).trans hu)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  exact ⟨P, hP (mem_zpowers u)⟩

omit [Finite G] in
private theorem sylow_eq_of_common (hG : InvolutionOddSpectrum G)
    (P Q : Sylow 2 G) {u : G} (huP : u ∈ P) (huQ : u ∈ Q) (hu : u ≠ 1) : P = Q := by
  apply Sylow.ext
  exact (hG.centralizer_eq_sylow P huP hu).symm.trans (hG.centralizer_eq_sylow Q huQ hu)

omit [Finite G] in
private theorem involutions_cross_isConj (hG : InvolutionOddSpectrum G)
    (P Q : Sylow 2 G) (hne : P ≠ Q) {u v : G}
    (huP : u ∈ P) (hvQ : v ∈ Q) (hu : orderOf u = 2) (hv : orderOf v = 2) :
    IsConj u v := by
  have hus : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have hvs : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
  apply isConj_of_involutions_odd_product u v hus hvs
  rcases hG (u * v) with huv | ho
  · exfalso
    have huv' : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right (by
      simpa [pow_two, huv] using pow_orderOf_eq_one (u * v))
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hus)
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hvs)
    have hc : v * u = u * v := by simpa [mul_inv_rev, hui, hvi] using huv'
    have hvP : v ∈ P := by
      change v ∈ (P : Subgroup G)
      rw [← hG.centralizer_eq_sylow P huP (by intro he; simp [he] at hu)]
      exact mem_centralizer_singleton_iff.mpr hc
    exact hne (sylow_eq_of_common hG P Q hvP hvQ (by intro he; simp [he] at hv))
  · exact ho

variable [IsSimpleGroup G] [Group.IsPerfect G]

/-- All involutions belong to one conjugacy class. -/
theorem involutions_isConj (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) :
    IsConj u v := by
  obtain ⟨P, huP⟩ := involution_mem_sylow hu
  obtain ⟨Q, hvQ⟩ := involution_mem_sylow hv
  by_cases hPQ : P = Q
  · subst Q
    obtain ⟨R, hR⟩ := P.exists_ne_of_not_normal (hG.sylow_not_normal t ht P)
    obtain ⟨w, _, hw, _, _⟩ := hG.sylow_distinct_involutions t ht R
    have hwG : orderOf (w : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hw
    exact (involutions_cross_isConj hG P R hR.symm huP w.property hu hwG).trans
      (involutions_cross_isConj hG P R hR.symm hvQ w.property hv hwG).symm
  · exact involutions_cross_isConj hG P Q hPQ huP hvQ hu hv

/-- The subgroup fixing both marked Sylow subgroups. -/
def twoPoint (P Q : Sylow 2 G) : Subgroup G :=
  MulAction.stabilizer G P ⊓ MulAction.stabilizer G Q

omit [Finite G] [IsSimpleGroup G] [Group.IsPerfect G] in
@[simp] theorem mem_twoPoint (P Q : Sylow 2 G) (g : G) :
    g ∈ twoPoint P Q ↔ g • P = P ∧ g • Q = Q := Iff.rfl

/-- The conjugation representation of the actual two-point stabilizer on P. -/
noncomputable def twoPointConj (P Q : Sylow 2 G) : twoPoint P Q →* MulAut P :=
  (P : Subgroup G).normalizerMonoidHom.comp (Subgroup.inclusion (by
    intro d hd
    exact Sylow.smul_eq_iff_mem_normalizer.mp ((mem_twoPoint P Q d).mp hd).1))

omit [Finite G] [IsSimpleGroup G] [Group.IsPerfect G] in
@[simp] theorem twoPointConj_coe (P Q : Sylow 2 G) (d : twoPoint P Q) (x : P) :
    (twoPointConj P Q d x : G) = (d : G) * (x : G) * (d : G)⁻¹ := rfl

/-- The two-point stabilizer conjugates any nonidentity root element to any other. -/
theorem twoPoint_conj_transitive (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (u v : P) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ d : twoPoint P Q, (d : G) * (u : G) * (d : G)⁻¹ = v := by
  let : IsElementaryAbelian 2 P := (hG.subgroup P).elementaryAbelian P.isPGroup'
  have hord (x : P) (hx : x ≠ 1) : orderOf (x : G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property)
      (by intro he; exact hx (Subtype.ext he))
  obtain ⟨g, hg⟩ := isConj_iff.mp (hG.involutions_isConj t ht (hord u hu) (hord v hv))
  obtain ⟨a, ha, hau⟩ := P.conj_eq_normalizer_conj_of_mem (u : G) g⁻¹ u.property
    (by simpa using hg ▸ v.property)
  have hav : a⁻¹ * (u : G) * a = v := by simpa using hau.symm.trans (by simpa using hg)
  have haP : a⁻¹ • P = P := Sylow.smul_eq_iff_mem_normalizer.mpr (inv_mem ha)
  have haQ : a⁻¹ • Q ≠ P := by
    intro he
    exact hPQ (smul_left_cancel a⁻¹ (haP.trans he.symm))
  obtain ⟨x, hx, _⟩ := hG.sylow_regular t ht P (a⁻¹ • Q) Q haQ hPQ.symm
  have hxP : (x : G) • P = P := Sylow.smul_eq_iff_mem_normalizer.mpr (le_normalizer x.property)
  refine ⟨⟨(x : G) * a⁻¹, ?_⟩, ?_⟩
  · apply (mem_twoPoint P Q _).mpr
    exact ⟨by rw [mul_smul, haP, hxP], by simpa [mul_smul] using hx⟩
  · change ((x : G) * a⁻¹) * (u : G) * ((x : G) * a⁻¹)⁻¹ = v
    calc
      _ = (x : G) * (a⁻¹ * (u : G) * a) * (x : G)⁻¹ := by group
      _ = (x : G) * (v : G) * (x : G)⁻¹ := by rw [hav]
      _ = v := by
        have hc : (x : G) * (v : G) = (v : G) * (x : G) :=
          congrArg Subtype.val (mul_comm' x v)
        rw [hc, mul_inv_cancel_right]


omit [IsSimpleGroup G] [Group.IsPerfect G] in
/-- A two-point stabilizer element centralizing a nonidentity root element is trivial. -/
theorem twoPoint_conj_eq_one (hG : InvolutionOddSpectrum G)
    (P Q : Sylow 2 G) (hPQ : P ≠ Q) (d : twoPoint P Q)
    (u : P) (hu : u ≠ 1) (hdu : (d : G) * (u : G) * (d : G)⁻¹ = u) : d = 1 := by
  have hc : (d : G) ∈ centralizer ({(u : G)} : Set G) :=
    mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul).mp hdu)
  have hdP : (d : G) ∈ (P : Subgroup G) := (hG.centralizer_eq_sylow P u.property
    (by intro he; exact hu (Subtype.ext he))) ▸ hc
  have he := P.eq_one_of_smul_eq_of_centralizer_le Q
    (fun _ hx hn => (hG.centralizer_eq_sylow P hx hn).le) hPQ.symm
    ⟨d, hdP⟩ ((mem_twoPoint P Q d).mp d.property).2
  exact Subtype.ext (congrArg (fun a : P => (a : G)) he)

/-- Conjugation on the nonidentity root elements is regular. -/
theorem twoPoint_conj_regular (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (u v : P) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃! d : twoPoint P Q, (d : G) * (u : G) * (d : G)⁻¹ = v := by
  obtain ⟨d, hd⟩ := hG.twoPoint_conj_transitive t ht P Q hPQ u v hu hv
  refine ⟨d, hd, fun e he => ?_⟩
  have hfix : ((d⁻¹ * e : twoPoint P Q) : G) * (u : G) *
      ((d⁻¹ * e : twoPoint P Q) : G)⁻¹ = u := by
    change ((d : G)⁻¹ * (e : G)) * (u : G) * ((d : G)⁻¹ * (e : G))⁻¹ = u
    calc
      _ = (d : G)⁻¹ * ((e : G) * (u : G) * (e : G)⁻¹) * (d : G) := by group
      _ = (d : G)⁻¹ * ((d : G) * (u : G) * (d : G)⁻¹) * (d : G) := by rw [he, hd]
      _ = u := by group
  exact (inv_mul_eq_one.mp (hG.twoPoint_conj_eq_one P Q hPQ (d⁻¹ * e) u hu hfix)).symm

omit [Finite G] [IsSimpleGroup G] [Group.IsPerfect G] in
/-- Every element of the two-point stabilizer has odd order. -/
theorem twoPoint_odd_order (hG : InvolutionOddSpectrum G)
    (P Q : Sylow 2 G) (hPQ : P ≠ Q) (d : twoPoint P Q) : Odd (orderOf (d : G)) := by
  rcases hG (d : G) with hd | hd
  · obtain ⟨R, hdR⟩ := involution_mem_sylow hd
    have hmem (T : Sylow 2 G) (hT : (d : G) • T = T) : (d : G) ∈ T := by
      have hh : (d : G) ∈ (R : Subgroup G) ⊓ normalizer (T : Set G) :=
        ⟨hdR, Sylow.smul_eq_iff_mem_normalizer.mp hT⟩
      rw [R.isPGroup'.inf_normalizer_sylow T] at hh
      exact hh.2
    have hfix := (mem_twoPoint P Q d).mp d.property
    exact (hPQ (sylow_eq_of_common hG P Q (hmem P hfix.1) (hmem Q hfix.2)
      (by intro he; simp [he] at hd))).elim
  · exact hd

/-- Double transitivity supplies an involution swapping the marked points. -/
theorem exists_twoPoint_swap (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q) :
    ∃ s : G, orderOf s = 2 ∧ s • P = Q ∧ s • Q = P := by
  obtain ⟨s, hsP, hsQ⟩ := MulAction.is_two_pretransitive_iff.mp
    (hG.sylowAction_two_pretransitive t ht) hPQ hPQ.symm
  refine ⟨s, ?_, hsP, hsQ⟩
  rcases hG s with hs | hs
  · exact hs
  · obtain ⟨k, hk⟩ := hs
    have hpow : ∀ k : ℕ, (s ^ (2 * k)) • P = P := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.mul_succ, pow_add, mul_smul, pow_two, mul_smul, hsP, hsQ, ih]
    have hp : P = Q := by
      calc
        P = (s ^ orderOf s) • P := by simp
        _ = (s ^ (2 * k + 1)) • P := by rw [hk]
        _ = s • ((s ^ (2 * k)) • P) := by rw [pow_succ', mul_smul]
        _ = Q := by rw [hpow, hsP]
    exact (hPQ hp).elim


omit [IsSimpleGroup G] [Group.IsPerfect G] in
/-- Every involution swapping the marked points inverts their abelian stabilizer. -/
theorem twoPoint_swap_structure (hG : InvolutionOddSpectrum G)
    (P Q : Sylow 2 G) (hPQ : P ≠ Q) (s : G) (hs : orderOf s = 2)
    (hsP : s • P = Q) (hsQ : s • Q = P) :
    IsMulCommutative (twoPoint P Q) ∧
      ∀ d : twoPoint P Q, s * (d : G) * s⁻¹ = (d : G)⁻¹ := by
  have hss : s * s = 1 := by simpa [pow_two, hs] using pow_orderOf_eq_one s
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hmem (d : twoPoint P Q) : s * (d : G) * s⁻¹ ∈ twoPoint P Q := by
    have hd := (mem_twoPoint P Q d).mp d.property
    apply (mem_twoPoint P Q _).mpr
    constructor
    · rw [mul_smul, mul_smul, hsi, hsP, hd.2, hsQ]
    · rw [mul_smul, mul_smul, hsi, hsQ, hd.1, hsP]
  let f : twoPoint P Q →* twoPoint P Q :=
    { toFun := fun d => ⟨s * (d : G) * s⁻¹, hmem d⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; simp [mul_assoc] }
  have hfi : Function.Involutive f := by
    intro d
    apply Subtype.ext
    change s * (s * (d : G) * s⁻¹) * s⁻¹ = d
    rw [hsi]
    calc
      _ = (s * s) * (d : G) * (s * s) := by group
      _ = d := by rw [hss]; simp
  have hff : MonoidHom.FixedPointFree f := by
    intro d hd
    have hdcomm : (d : G) ∈ centralizer ({s} : Set G) := by
      have he : s * (d : G) * s⁻¹ = d := congrArg Subtype.val hd
      exact mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul.mp he).symm)
    let : IsElementaryAbelian 2 (centralizer ({s} : Set G)) := hG.centralizer_elementaryAbelian hs
    have hd2 : (d : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (d : G) hdcomm
    have ho := hG.twoPoint_odd_order P Q hPQ d
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hd2) with h1 | h2
    · exact Subtype.ext (orderOf_eq_one_iff.mp h1)
    · exact (ho.not_two_dvd_nat (h2 ▸ dvd_rfl)).elim
  refine ⟨⟨⟨fun a b => (hff.commute_all_of_involutive hfi a b).eq⟩⟩, ?_⟩
  intro d
  exact congrArg Subtype.val (congrFun (hff.coe_eq_inv_of_involutive hfi) d)

/-- The actual two-point stabilizer is abelian. -/
theorem twoPoint_commutative (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q) :
    IsMulCommutative (twoPoint P Q) := by
  obtain ⟨s, hs, hsP, hsQ⟩ := hG.exists_twoPoint_swap t ht P Q hPQ
  exact (hG.twoPoint_swap_structure P Q hPQ s hs hsP hsQ).1

/-- The two-point stabilizer acts regularly on all remaining points. -/
theorem twoPoint_regular (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (R T : Sylow 2 G) (hRP : R ≠ P) (hRQ : R ≠ Q)
    (hTP : T ≠ P) (hTQ : T ≠ Q) :
    ∃! d : twoPoint P Q, (d : G) • R = T := by
  obtain ⟨u, hu, _⟩ := hG.sylow_regular t ht P Q R hPQ.symm hRP
  obtain ⟨v, hv, _⟩ := hG.sylow_regular t ht P Q T hPQ.symm hTP
  have hu1 : u ≠ 1 := by intro he; simp [he] at hu; exact hRQ hu.symm
  have hv1 : v ≠ 1 := by intro he; simp [he] at hv; exact hTQ hv.symm
  obtain ⟨d, hd⟩ := hG.twoPoint_conj_transitive t ht P Q hPQ u v hu1 hv1
  have hdQ := ((mem_twoPoint P Q d).mp d.property).2
  have hdR : (d : G) • R = T := by
    rw [← hu, ← hv, ← hd, mul_smul, mul_smul,
      inv_smul_eq_iff.mpr hdQ.symm]
  refine ⟨d, hdR, fun e he => ?_⟩
  have hfix : ∀ X : Sylow 2 G, (d : G) • X = (e : G) • X →
      (((d⁻¹ * e : twoPoint P Q) : G)) • X = X := by
    intro X hX
    change ((d : G)⁻¹ * (e : G)) • X = X
    rw [mul_smul, ← hX, inv_smul_smul]
  by_contra hne
  have hneG : ((d⁻¹ * e : twoPoint P Q) : G) ≠ 1 := by
    intro heq
    exact hne (inv_mul_eq_one.mp (show d⁻¹ * e = 1 from Subtype.ext heq)).symm
  apply hG.sylowAction_at_most_two_fixed t ht _ hneG P Q R hPQ hRP.symm hRQ.symm
  have hdFix := (mem_twoPoint P Q d).mp d.property
  have heFix := (mem_twoPoint P Q e).mp e.property
  exact ⟨hfix P (hdFix.1.trans heFix.1.symm),
    hfix Q (hdFix.2.trans heFix.2.symm), hfix R (hdR.trans he.symm)⟩

end Theory.GroupTheory.InvolutionOddSpectrum

end
