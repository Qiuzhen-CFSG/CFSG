module

public import Theory.GroupAction.FourthPowerFixed
public import Mathlib.GroupTheory.Index

/-!
# Lifting a marked binary Jordan chain

Let an elementary binary group map onto elementary sixteen, compatibly
with automorphisms of fourth power one. If the quotient automorphism has
two fixed points, its displacement has a regular length-four chain.
A prescribed nonidentity fixed point and a prescribed preimage of it
can be retained as the last two quotient coordinates.

Iterated kernel counts produce a top vector. Multiplying that vector by
its displacement removes a possible fixed-point term in the prescribed
second coordinate. Lift the resulting top vector and take successive
displacements upstairs. Fourth power one makes the last lift actually
fixed, even though a general lift of a quotient fixed point need not be.
The first displacement lies in every invariant subgroup of index two.

This supplies the lifting step for the matrix calculation and equation (1)
in D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.674 and 678, without assumptions about an ambient finite group.
-/

open Subgroup
open scoped IsMulCommutative

namespace Theory.GroupAction

private theorem card_ker_comp_le
    {A B C : Type*} [Group A] [Group B] [Group C] [Finite A] [Finite B]
    (f : B →* C) (g : A →* B) :
    Nat.card (f.comp g).ker ≤ Nat.card g.ker * Nat.card f.ker := by
  let r : (f.comp g).ker →* B := g.comp (f.comp g).ker.subtype
  have hk : Nat.card r.ker ≤ Nat.card g.ker := by
    let i : r.ker → g.ker := fun x => ⟨x.val.val, x.property⟩
    exact Nat.card_le_card_of_injective i (by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun x : g.ker => (x : A)) hxy)))
  have hr : r.range ≤ f.ker := by
    rintro _ ⟨x, rfl⟩
    exact x.property
  have hc := r.ker.card_mul_index
  rw [index_ker] at hc
  exact hc.symm.le.trans (Nat.mul_le_mul hk (card_le_of_le hr))

private theorem exists_marked_nilpotent_chain
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (s : W →* W) (hW : Nat.card W = 16) (hker : Nat.card s.ker = 2)
    (hfour : ∀ w, s (s (s (s w))) = 1)
    (t v : W) (ht : t ≠ 1) (hst : s t = 1) (hsv : s v = t) :
    ∃ w : W, s (s w) = v ∧ s (s (s w)) = t := by
  have hbound : Nat.card (s.comp (s.comp s)).ker ≤ 8 := by
    have h1 := card_ker_comp_le s s
    have h2 := card_ker_comp_le s (s.comp s)
    rw [hker] at h1 h2
    omega
  have hex : ∃ w, s (s (s w)) ≠ 1 := by
    by_contra hn
    have hall : ∀ w, s (s (s w)) = 1 := by simpa using hn
    have heq : (s.comp (s.comp s)).ker = ⊤ := by
      ext w
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, mem_top, iff_true]
      exact hall w
    rw [heq, card_top, hW] at hbound
    omega
  obtain ⟨w, hw⟩ := hex
  obtain ⟨_, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : s.ker)).mp hker
  have unique (r : W) (hr : s r = 1) (hne : r ≠ 1) : r = t := by
    have heq : (⟨r, hr⟩ : s.ker) = ⟨t, hst⟩ :=
      (huniq _ (fun heq => hne (congrArg Subtype.val heq))).trans
        (huniq _ (fun heq => ht (congrArg Subtype.val heq))).symm
    exact congrArg Subtype.val heq
  have hwt : s (s (s w)) = t := unique _ (hfour w) hw
  have hdiff : s (v / s (s w)) = 1 := by
    rw [map_div, hsv, hwt]
    simp only [div_eq_mul_inv, mul_inv_cancel]
  by_cases heq : v / s (s w) = 1
  · exact ⟨w, (div_eq_one.mp heq).symm, hwt⟩
  · have hd := unique _ hdiff heq
    have hv : v = s (s w) * t := by
      have hh := (div_eq_iff_eq_mul).mp hd
      exact hh.trans (mul_comm _ _)
    refine ⟨w * s w, ?_, ?_⟩
    · simp only [map_mul, hwt]
      exact hv.symm
    · simp only [map_mul, hwt, hst, mul_one]

private theorem displacement_four
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (a : MulAut V) (ha4 : a ^ 4 = 1) :
    ∃ s : V →* V, (∀ w, s w = a w * w) ∧
      s.ker = FixedPoints.subgroup (zpowers a) V ∧
      ∀ w, s (s (s (s w))) = 1 := by
  have hself (w : V) : w * w = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) w
  have hinv (w : V) : w⁻¹ = w := inv_eq_of_mul_eq_one_left (hself w)
  let s : V →* V := {
    toFun := fun w => a w * w
    map_one' := by simp
    map_mul' := by intros; simp only [map_mul]; ac_rfl }
  refine ⟨s, fun _ => rfl, ?_, ?_⟩
  · ext w
    rw [MonoidHom.mem_ker, MulAut.mem_fixed_zpowers_iff]
    change a w * w = 1 ↔ a w = w
    rw [mul_eq_one_iff_eq_inv, hinv]
  · intro w
    have htwo (w : V) : s (s w) = a (a w) * w := by
      change a (a w * w) * (a w * w) = _
      rw [map_mul]
      calc
        _ = (a (a w) * w) * (a w * a w) := by ac_rfl
        _ = _ := by rw [hself, mul_one]
    rw [htwo, htwo]
    have hfour : a (a (a (a w))) = w := congrArg (fun b : MulAut V => b w) ha4
    rw [map_mul, map_mul, hfour]
    calc
      _ = (w * w) * (a (a w) * a (a w)) := by ac_rfl
      _ = 1 := by rw [hself, hself, mul_one]

/-- A regular quotient chain lifts to an exact chain, retaining the two
marked quotient coordinates and the prescribed invariant hyperplane. -/
public theorem marked_jordan_chain_lift
    {V W : Type*} [Group V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (a : MulAut V) (b : MulAut W) (q : V →* W) (hq : Function.Surjective q)
    (ha4 : a ^ 4 = 1) (hcompat : ∀ w, q (a w) = b (q w))
    (hW : Nat.card W = 16)
    (hfixed : Nat.card (FixedPoints.subgroup (zpowers b) W) = 2)
    (t v : V) (ht : q t ≠ 1) (hbt : b (q t) = q t)
    (hbv : b (q v) * q v = q t)
    (U : Subgroup V) (hU : U.index = 2) (hstable : ∀ u ∈ U, a u ∈ U) :
    ∃ t0 v0 u w : V,
      q t0 = q t ∧ q v0 = q v ∧ u ∈ U ∧
      a t0 * t0 = 1 ∧ a v0 * v0 = t0 ∧
      a u * u = v0 ∧ a w * w = u := by
  have hb4 : b ^ 4 = 1 := by
    ext y
    obtain ⟨w, rfl⟩ := hq y
    have hfour : a (a (a (a w))) = w := congrArg (fun c : MulAut V => c w) ha4
    have heq := congrArg q hfour
    change b (b (b (b (q w)))) = q w
    simpa only [hcompat] using heq
  obtain ⟨s, hs, _, hs4⟩ := displacement_four a ha4
  obtain ⟨r, hr, hrker, hr4⟩ := displacement_four b hb4
  have hqr (w : V) : q (s w) = r (q w) := by
    rw [hs, map_mul, hcompat, hr]
  have hst : r (q t) = 1 := by
    rw [hr, hbt]
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) (q t)
  have hsv : r (q v) = q t := by rw [hr]; exact hbv
  obtain ⟨wbar, hwv, hwt⟩ := exists_marked_nilpotent_chain r hW
    (hrker ▸ hfixed) hr4 (q t) (q v) ht hst hsv
  obtain ⟨w, rfl⟩ := hq wbar
  have hu : s w ∈ U := by
    rw [hs]
    apply (U.mul_mem_iff_of_index_two hU).mpr
    constructor
    · intro hw
      have hfour : a (a (a (a w))) = w := congrArg (fun c : MulAut V => c w) ha4
      simpa only [hfour] using hstable _ (hstable _ (hstable _ hw))
    · exact hstable w
  refine ⟨s (s (s w)), s (s w), s w, w, ?_, ?_, hu, ?_, ?_, ?_, ?_⟩
  · simpa only [hqr] using hwt
  · simpa only [hqr] using hwv
  · rw [← hs]; exact hs4 w
  · exact (hs _).symm
  · exact (hs _).symm
  · exact (hs _).symm

end Theory.GroupAction
