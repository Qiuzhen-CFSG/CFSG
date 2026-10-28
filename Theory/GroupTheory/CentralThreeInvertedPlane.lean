module
public import Theory.GroupTheory.CentralCoprimeLiftUnique
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Data.ZMod.Basic

/-!
# Elementary nine lifts across central three-kernels

A cubic element inverted in the quotient lifts to a cubic element: take the
commutator of arbitrary lifts of the inverter and that element. If the
inverter has order four, its unique coprime torsion lift forces this cubic
lift to centralize every lift of the commuting, fixed coordinate. Two
independently inverted coordinates therefore give an elementary nine.

A nonidentity involution centralizing both quotient coordinates has a unique
involutory lift. It centralizes the constructed nine, giving a nontrivial
two-subgroup whose normalizer contains that nine. All splitting and power
relations are proved here; the concrete quotient configuration is explicit.

The application is the McL three-cover case of Aschbacher--Smith A.2.19,
printed p.41 (PDF52). This argument retains the two-local witness missing
from the ordinary-rank statement of I.2.1, printed p.409.
-/

public section
namespace MonoidHom
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H]

/-- Coprime torsion lifts commute whenever their images commute. -/
theorem commute_of_map_commute_of_coprime_torsion
    (q : G →* H) (hc : q.ker ≤ Subgroup.center G) {p n : ℕ}
    (hp : IsPGroup p q.ker) (hn : Nat.Coprime p n)
    (u v : G) (hu : u ^ n = 1) (huv : Commute (q u) (q v)) :
    Commute u v := by
  have he : v * u * v⁻¹ = u :=
    q.eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker hc hp hn
      (by simp only [map_mul, map_inv]; rw [← huv.eq]; group)
      (by rw [conj_pow, hu]; simp) hu
  exact ((mul_inv_eq_iff_eq_mul).mp he).symm

/-- Inversion of a cubic image constructs an actual cubic lift as a commutator. -/
theorem inverted_cubic_commutator_lift
    (q : G →* H) (hc : q.ker ≤ Subgroup.center G)
    (u r : G) (hu : q u ^ 3 = 1)
    (hr : q r * q u * (q r)⁻¹ = (q u)⁻¹) :
    q ⁅r, u⁆ = q u ∧ ⁅r, u⁆ ^ 3 = 1 := by
  have hk : r * u * r⁻¹ * u ∈ q.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hr, inv_mul_cancel]
  have hkcomm : Commute (r * u * r⁻¹ * u) u :=
    (Subgroup.mem_center_iff.mp (hc hk) u).symm
  have hcomm : Commute (r * u * r⁻¹) u := by
    have hh := hkcomm.mul_left (Commute.refl u).inv_left
    simpa only [mul_inv_cancel_right] using hh
  have hu3 : u ^ 3 ∈ q.ker := by
    simpa only [MonoidHom.mem_ker, map_pow] using hu
  have hr3 : r * u ^ 3 * r⁻¹ = u ^ 3 := by
    rw [Subgroup.mem_center_iff.mp (hc hu3) r]
    group
  constructor
  · change q (r * u * r⁻¹ * u⁻¹) = q u
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hr]
    have he : q u * q u * q u = 1 := by simpa only [pow_succ, pow_zero, one_mul] using hu
    calc
      (q u)⁻¹ * (q u)⁻¹ = (q u)⁻¹ * (q u)⁻¹ * (q u * q u * q u) := by rw [he, mul_one]
      _ = q u := by group
  · change (r * u * r⁻¹ * u⁻¹) ^ 3 = 1
    rw [hcomm.inv_right.mul_pow, conj_pow, inv_pow, hr3, mul_inv_cancel]

/-- A partial inverter of order prime to three produces a cubic lift
centralizing every lift of an image fixed by the inverter and the cubic. -/
theorem exists_cubic_lift_centralizing_of_partial_inverter
    (q : G →* H) (hq : Function.Surjective q)
    (hc : q.ker ≤ Subgroup.center G) (hp : IsPGroup 3 q.ker)
    (x r : H) (hx : x ^ 3 = 1) (hr : r ^ 4 = 1)
    (hrx : r * x * r⁻¹ = x⁻¹) :
    ∃ u : G, q u = x ∧ u ^ 3 = 1 ∧
      ∀ v : G, Commute x (q v) → Commute r (q v) → Commute u v := by
  obtain ⟨R, hR, hR4⟩ :=
    q.exists_pow_eq_one_lift_of_central_pgroup_ker hq hc hp (by decide : Nat.Coprime 3 4) r hr
  obtain ⟨U, hU⟩ := hq x
  have h := q.inverted_cubic_commutator_lift hc U R (by rw [hU]; exact hx)
    (by rw [hR, hU]; exact hrx)
  refine ⟨⁅R, U⁆, h.1.trans hU, h.2, ?_⟩
  intro v hxv hrv
  have hRv : Commute R v := q.commute_of_map_commute_of_coprime_torsion
    hc hp (by decide : Nat.Coprime 3 4) R v hR4 (by rwa [hR])
  have hUrv : Commute (U * R⁻¹ * U⁻¹) v := by
    apply q.commute_of_map_commute_of_coprime_torsion hc hp
      (by decide : Nat.Coprime 3 4) _ v
    · rw [conj_pow, inv_pow, hR4, inv_one]
      simp
    · simp only [map_mul, map_inv, hU, hR]
      exact (hxv.mul_left hrv.inv_left).mul_left hxv.inv_left
  simpa only [commutatorElement_def, mul_assoc] using hRv.mul_left hUrv

/-- The coordinate homomorphism of two commuting cubic elements. -/
@[expose] def cubicPairHom (u v : G) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (huv : Commute u v) : Multiplicative (ZMod 3 × ZMod 3) →* G where
  toFun a := u ^ a.toAdd.1.val * v ^ a.toAdd.2.val
  map_one' := by simp
  map_mul' a b := by
    change u ^ (a.toAdd.1 + b.toAdd.1).val * v ^ (a.toAdd.2 + b.toAdd.2).val = _
    rw [ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ hu, ← pow_eq_pow_mod _ hv,
      pow_add, pow_add]
    exact (huv.pow_pow b.toAdd.1.val a.toAdd.2.val).mul_mul_mul_comm _ _

/-- An elementary nine with independent inversion supplies an elementary-nine
lift in a genuine two-local of every central three-extension. -/
theorem exists_two_local_cubicPair_lift
    (q : G →* H) (hq : Function.Surjective q)
    (hc : q.ker ≤ Subgroup.center G) (hp : IsPGroup 3 q.ker)
    (x y r s t : H) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : Commute x y)
    (hinj : Function.Injective (cubicPairHom x y hx hy hxy))
    (hr : r ^ 4 = 1) (hrx : r * x * r⁻¹ = x⁻¹) (hry : Commute r y)
    (hsy : s * y * s⁻¹ = y⁻¹)
    (ht : t ^ 2 = 1) (htne : t ≠ 1) (hxt : Commute x t) (hyt : Commute y t) :
    ∃ (Q : Subgroup G) (f : Multiplicative (ZMod 3 × ZMod 3) →* G),
      Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ Function.Injective (q.comp f) ∧
      ∀ a, f a ∈ Subgroup.normalizer (Q : Set G) := by
  obtain ⟨U, hU, hU3, hUc⟩ := q.exists_cubic_lift_centralizing_of_partial_inverter
    hq hc hp x r hx hr hrx
  obtain ⟨Y, hY⟩ := hq y
  obtain ⟨S, hS⟩ := hq s
  have hV := q.inverted_cubic_commutator_lift hc Y S (by rw [hY]; exact hy)
    (by rw [hY, hS]; exact hsy)
  let V := ⁅S, Y⁆
  have hVq : q V = y := hV.1.trans hY
  have hUV : Commute U V := hUc V (by rwa [hVq]) (by rwa [hVq])
  let f := cubicPairHom U V hU3 hV.2 hUV
  obtain ⟨T, hTq, hT2⟩ := q.exists_pow_eq_one_lift_of_central_pgroup_ker
    hq hc hp (by decide : Nat.Coprime 3 2) t ht
  have hTne : T ≠ 1 := by
    intro h
    apply htne
    rw [← hTq, h, map_one]
  have hTU : Commute T U := q.commute_of_map_commute_of_coprime_torsion
    hc hp (by decide : Nat.Coprime 3 2) T U hT2 (by rw [hTq, hU]; exact hxt.symm)
  have hTV : Commute T V := q.commute_of_map_commute_of_coprime_torsion
    hc hp (by decide : Nat.Coprime 3 2) T V hT2 (by rw [hTq, hVq]; exact hyt.symm)
  refine ⟨Subgroup.zpowers T, f, ?_, ?_, ?_, ?_⟩
  · intro he
    apply hTne
    simpa only [he, Subgroup.mem_bot] using Subgroup.mem_zpowers T
  · apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime hT2 hTne, pow_one]
  · intro a b hab
    apply hinj
    change q (U ^ a.toAdd.1.val * V ^ a.toAdd.2.val) =
      q (U ^ b.toAdd.1.val * V ^ b.toAdd.2.val) at hab
    change x ^ a.toAdd.1.val * y ^ a.toAdd.2.val =
      x ^ b.toAdd.1.val * y ^ b.toAdd.2.val
    simpa only [map_mul, map_pow, hU, hVq] using hab
  · intro a
    apply Subgroup.centralizer_le_normalizer
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (((hTU.pow_right a.toAdd.1.val).mul_right
      (hTV.pow_right a.toAdd.2.val)).zpow_left n).eq

end MonoidHom
