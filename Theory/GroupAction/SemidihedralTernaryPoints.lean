module

public import Theory.GroupAction.PrimeOrderPoints
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# The three semidihedral orbits on ternary projective points

A group of order sixteen acts on an elementary abelian group of order
27. An order-eight rotation has central fourth power z, with a fixed
line B. A commuting involution f inverts B and has a fixed line F.
The literal image action on order-three subgroups has exactly three
orbits, of lengths one, four and eight. The stabilizer of F is <z,f>.

If the rotation's square stabilizes a ternary line, its fourth power
fixes that line pointwise, so the line is B. Thus the F-orbit has at
least four points; <z,f> gives the matching upper bound. A product of
nonidentity elements of B and F generates a line moved by z, and hence
with rotation period eight. Disjointness and the thirteen-point count
complete the exhaustive partition. Only the central fourth power and
the specified involution action are needed from the semidihedral data.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
J.2.7, printed p.437 (PDF p.448).
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace SemidihedralTernaryPoints
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 3 E]

omit [Finite E] in
private theorem cube (x : E) : x ^ 3 = 1 :=
  Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 3 E) x

omit [Finite E] in
private theorem square_eq_inv (x : E) : x ^ 2 = x⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  simpa only [← pow_succ] using cube x

omit [Finite E] in
private theorem eq_one_of_eq_inv {x : E} (h : x = x⁻¹) : x = 1 := by
  have h2 : x ^ 2 = 1 := by simpa only [pow_two] using (eq_inv_iff_mul_eq_one.mp h)
  have h3 := cube x
  rwa [pow_succ, h2, one_mul] at h3

private theorem point_eq_zpowers (U : OrderPoints 3 E) {x : E}
    (hx : x ∈ U.val) (hne : x ≠ 1) : U.val = zpowers x := by
  apply (eq_of_le_of_card_ge (zpowers_le.mpr hx) ?_).symm
  rw [Nat.card_zpowers, orderOf_eq_prime (cube x) hne, U.property]

private theorem point_mem_cases (U : OrderPoints 3 E) {x y : E}
    (hx : x ∈ U.val) (hne : x ≠ 1) (hy : y ∈ U.val) :
    y = 1 ∨ y = x ∨ y = x⁻¹ := by
  classical
  rw [point_eq_zpowers U hx hne, mem_zpowers_iff_mem_range_orderOf,
    orderOf_eq_prime (cube x) hne, Finset.mem_image] at hy
  obtain ⟨n, hn, rfl⟩ := hy
  have hn' : n < 3 := Finset.mem_range.mp hn
  interval_cases n <;> simp [square_eq_inv]

private theorem stable_apply_cases (a : MulAut E) (U : OrderPoints 3 E)
    (hU : U.val.map a.toMonoidHom = U.val) {x : E} (hx : x ∈ U.val) :
    a x = x ∨ a x = x⁻¹ := by
  by_cases hne : x = 1
  · simp [hne]
  have hy : a x ∈ U.val := hU ▸ mem_map_of_mem a.toMonoidHom hx
  rcases point_mem_cases U hx hne hy with h | h | h
  · exact (hne (a.injective (h.trans (map_one a).symm))).elim
  · exact Or.inl h
  · exact Or.inr h

private theorem stable_square_fixed (a : MulAut E) (U : OrderPoints 3 E)
    (hU : U.val.map a.toMonoidHom = U.val) {x : E} (hx : x ∈ U.val) :
    (a ^ 2) x = x := by
  change a (a x) = x
  rcases stable_apply_cases a U hU hx with h | h
  · rw [h, h]
  · rw [h, map_inv, h, inv_inv]

section Period
variable {A X : Type*} [Group A] [MulAction A X] [Finite X]

private theorem period_le_orbit (r : A) (x : X) :
    MulAction.period r x ≤ Nat.card (MulAction.orbit A x) := by
  let j : Fin (MulAction.period r x) → MulAction.orbit A x :=
    fun i => ⟨r ^ (i : ℕ) • x, ⟨r ^ (i : ℕ), rfl⟩⟩
  have hj : Function.Injective j := by
    intro i k hik
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod i.isLt k.isLt
    simpa only [smul_iterate_apply] using congrArg Subtype.val hik
  simpa using Nat.card_le_card_of_injective j hj

omit [Finite X] in
private theorem period_four_le (r : A) (x : X) (hr : r ^ 8 = 1)
    (hx : r ^ 2 • x ≠ x) : 4 ≤ MulAction.period r x := by
  have hd : MulAction.period r x ∣ 8 :=
    MulAction.pow_smul_eq_iff_period_dvd.mp (by rw [hr, one_smul])
  have hn : ¬ MulAction.period r x ∣ 2 :=
    fun h => hx (MulAction.pow_smul_eq_iff_period_dvd.mpr h)
  have hcases : MulAction.period r x = 1 ∨ MulAction.period r x = 2 ∨
      MulAction.period r x = 4 ∨ MulAction.period r x = 8 := by
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (show MulAction.period r x ∣ 2 ^ 3 from hd)
    interval_cases k <;> simp_all
  rcases hcases with h | h | h | h <;> simp_all

omit [Finite X] in
private theorem period_eight (r : A) (x : X) (hr : r ^ 8 = 1)
    (hx : r ^ 4 • x ≠ x) : MulAction.period r x = 8 := by
  have hd : MulAction.period r x ∣ 8 :=
    MulAction.pow_smul_eq_iff_period_dvd.mp (by rw [hr, one_smul])
  have hn : ¬ MulAction.period r x ∣ 4 :=
    fun h => hx (MulAction.pow_smul_eq_iff_period_dvd.mpr h)
  have hcases : MulAction.period r x = 1 ∨ MulAction.period r x = 2 ∨
      MulAction.period r x = 4 ∨ MulAction.period r x = 8 := by
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (show MulAction.period r x ∣ 2 ^ 3 from hd)
    interval_cases k <;> simp_all
  rcases hcases with h | h | h | h <;> simp_all

end Period

private theorem disjoint_orbits {A X : Type*} [Group A] [MulAction A X]
    (x y : X) (h : y ∉ MulAction.orbit A x) :
    Disjoint (MulAction.orbit A x) (MulAction.orbit A y) := by
  apply Set.disjoint_left.mpr
  intro v hvx hvy
  have he := (MulAction.orbit_eq_iff.mpr hvy).symm.trans
    (MulAction.orbit_eq_iff.mpr hvx)
  exact h (MulAction.orbit_eq_iff.mp he)

private theorem central_fixed_on_orbit {A X : Type*} [Group A] [MulAction A X]
    (z : A) (hz : z ∈ center A) (x : X) (hx : z • x = x) :
    ∀ y ∈ MulAction.orbit A x, z • y = y := by
  rintro _ ⟨a, rfl⟩
  rw [← mul_smul, (mem_center_iff.mp hz a).symm, mul_smul, hx]

private theorem point_nontrivial (U : OrderPoints 3 E) :
    ∃ x : E, x ∈ U.val ∧ x ≠ 1 := by
  let : Nontrivial U.val := Finite.one_lt_card_iff_nontrivial.mp (by rw [U.property]; decide)
  obtain ⟨x, hx⟩ := exists_ne (1 : U.val)
  exact ⟨x, x.property, fun h => hx (Subtype.ext h)⟩

omit [IsElementaryAbelian 3 E] in
private theorem fixed_stable {A : Type*} [Group A] (ρ : A →* MulAut E)
    (f t : A) (hcomm : Commute f t) :
    (ρ f).fixedSubgroup.map (ρ t).toMonoidHom = (ρ f).fixedSubgroup := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    have he := congrArg (fun a : MulAut E => a x) ((hcomm.map ρ).eq)
    change ρ f (ρ t x) = ρ t (ρ f x) at he
    exact he.trans (congrArg (ρ t) ((MulAut.mem_fixedSubgroup _ _).mp hx))
  · rw [card_map_of_injective (ρ t).injective]

private theorem square_stable_eq_base {A : Type*} [Group A] (ρ : A →* MulAut E)
    (r z : A) (hrz : r ^ 4 = z) (B U : OrderPoints 3 E)
    (hB : (ρ z).fixedSubgroup = B.val)
    (hU : U.val.map (ρ (r ^ 2)).toMonoidHom = U.val) : U = B := by
  apply Subtype.ext
  apply eq_of_le_of_card_ge
  · intro x hx
    rw [← hB, MulAut.mem_fixedSubgroup]
    have he : ρ (r ^ 2) ^ 2 = ρ z := by
      rw [← map_pow, ← pow_mul, show 2 * 2 = 4 from rfl, hrz]
    rw [← he]
    exact stable_square_fixed (ρ (r ^ 2)) U hU hx
  · rw [U.property, B.property]

private theorem fixed_ne_base {A : Type*} [Group A] (ρ : A →* MulAut E)
    (f : A) (B F : OrderPoints 3 E)
    (hF : (ρ f).fixedSubgroup = F.val)
    (hinv : ∀ b ∈ B.val, ρ f b = b⁻¹) : F ≠ B := by
  intro he
  obtain ⟨x, hx, hne⟩ := point_nontrivial F
  have hf : ρ f x = x := (MulAut.mem_fixedSubgroup _ _).mp (hF.symm ▸ hx)
  have hb : x ∈ B.val := he ▸ hx
  exact hne (eq_one_of_eq_inv (hf.symm.trans (hinv x hb)))

private theorem exists_moved_point {A : Type*} [Group A] (ρ : A →* MulAut E)
    (z f : A) (B F : OrderPoints 3 E)
    (hB : (ρ z).fixedSubgroup = B.val) (hF : (ρ f).fixedSubgroup = F.val)
    (hcomm : Commute f z) (hinv : ∀ b ∈ B.val, ρ f b = b⁻¹) :
    ∃ U : OrderPoints 3 E, U.val.map (ρ z).toMonoidHom ≠ U.val := by
  obtain ⟨b, hb, hbne⟩ := point_nontrivial B
  obtain ⟨x, hx, hxne⟩ := point_nontrivial F
  have hzb : ρ z b = b := (MulAut.mem_fixedSubgroup _ _).mp (hB.symm ▸ hb)
  have hfx : ρ f x = x := (MulAut.mem_fixedSubgroup _ _).mp (hF.symm ▸ hx)
  have hstable : F.val.map (ρ z).toMonoidHom = F.val := by
    rw [← hF]
    exact fixed_stable ρ f z hcomm
  have hzx : ρ z x = x⁻¹ := by
    rcases stable_apply_cases (ρ z) F hstable hx with h | h
    · have hxB : x ∈ B.val := hB ▸ (MulAut.mem_fixedSubgroup _ _).mpr h
      exact (hxne (eq_one_of_eq_inv (hfx.symm.trans (hinv x hxB)))).elim
    · exact h
  have hmove : ρ z (b * x) ≠ b * x := by
    rw [map_mul, hzb, hzx]
    intro he
    exact hxne (eq_one_of_eq_inv (mul_left_cancel he).symm)
  have hnotinv : ρ z (b * x) ≠ (b * x)⁻¹ := by
    rw [map_mul, hzb, hzx, mul_inv_rev, mul_comm x⁻¹ b⁻¹]
    intro he
    exact hbne (eq_one_of_eq_inv (mul_right_cancel he))
  have hne : b * x ≠ 1 := by
    intro he
    apply hmove
    rw [he, map_one]
  let U : OrderPoints 3 E := ⟨zpowers (b * x), by
    rw [Nat.card_zpowers, orderOf_eq_prime (cube (b * x)) hne]⟩
  refine ⟨U, fun h => ?_⟩
  exact (stable_apply_cases (ρ z) U h (mem_zpowers _)).elim hmove hnotinv

/-- The full 1,4,8 partition for the original subgroup-image action, including
pairwise disjointness, exhaustion, and the literal four-group stabilizer.
The rotation and central involution are retained as elements of the original
actor group; no abstract replacement action or orbit premise is used. -/
theorem partition {A : Type*} [Group A] [Finite A]
    (ρ : A →* MulAut E) (hA : Nat.card A = 16) (hE : Nat.card E = 27)
    (r z f : A) (hr : r ^ 8 = 1) (hrz : r ^ 4 = z)
    (hz : orderOf z = 2) (hf : orderOf f = 2) (hzc : z ∈ center A)
    (B F : OrderPoints 3 E)
    (hBinv : ∀ a, B.val.map (ρ a).toMonoidHom = B.val)
    (hB : (ρ z).fixedSubgroup = B.val) (hF : (ρ f).fixedSubgroup = F.val)
    (hinv : ∀ b ∈ B.val, ρ f b = b⁻¹) :
    OrderPoints.orbit ρ B = {B} ∧
    Nat.card (OrderPoints.orbit ρ B) = 1 ∧
    Nat.card (OrderPoints.orbit ρ F) = 4 ∧
    OrderPoints.stabilizer ρ F = closure ({z, f} : Set A) ∧
    (OrderPoints.stabilizer ρ F).index = 4 ∧
    ∃ U : OrderPoints 3 E,
      Nat.card (OrderPoints.orbit ρ U) = 8 ∧
      Disjoint (OrderPoints.orbit ρ B) (OrderPoints.orbit ρ F) ∧
      Disjoint (OrderPoints.orbit ρ B) (OrderPoints.orbit ρ U) ∧
      Disjoint (OrderPoints.orbit ρ F) (OrderPoints.orbit ρ U) ∧
      OrderPoints.orbit ρ B ∪ OrderPoints.orbit ρ F ∪ OrderPoints.orbit ρ U = Set.univ := by
  let := OrderPoints.action (p := 3) ρ
  have : Finite (OrderPoints 3 E) := Nat.finite_of_card_ne_zero
    (by rw [OrderPoints.card_thirteen hE]; decide)
  have hBF : F ≠ B := fixed_ne_base ρ f B F hF hinv
  have hcomm : Commute f z := mem_center_iff.mp hzc f
  have hzf : z ≠ f := by
    intro he
    apply hBF
    apply Subtype.ext
    rw [← hF, ← he, hB]
  let K : Subgroup A := closure ({z, f} : Set A)
  let : IsKleinFour K := isKleinFour_closure_pair_of_orderOf z f hz hf hzf hcomm.symm
  have hK : Nat.card K = 4 := IsKleinFour.card_four
  have hzF : z • F = F := by
    apply Subtype.ext
    change F.val.map (ρ z).toMonoidHom = F.val
    rw [← hF]
    exact fixed_stable ρ f z hcomm
  have hfF : f • F = F := by
    apply Subtype.ext
    change F.val.map (ρ f).toMonoidHom = F.val
    rw [← hF]
    exact fixed_stable ρ f f (Commute.refl f)
  have hKle : K ≤ MulAction.stabilizer A F := by
    apply (closure_le _).mpr
    intro a ha
    rcases (show a = z ∨ a = f by simpa using ha) with rfl | rfl
    · exact hzF
    · exact hfF
  have hfour : 4 ≤ Nat.card (MulAction.stabilizer A F) :=
    hK ▸ card_le_of_le hKle
  have hsquare : r ^ 2 • F ≠ F := by
    intro he
    exact hBF (square_stable_eq_base ρ r z hrz B F hB (congrArg Subtype.val he))
  have hlower : 4 ≤ Nat.card (MulAction.orbit A F) :=
    (period_four_le r F hr hsquare).trans (period_le_orbit r F)
  have hcount := (MulAction.stabilizer A F).index_mul_card
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hA] at hcount
  have hFcard : Nat.card (MulAction.orbit A F) = 4 := by nlinarith
  have hstabcard : Nat.card (MulAction.stabilizer A F) = 4 := by nlinarith
  have hstab : MulAction.stabilizer A F = K :=
    (eq_of_le_of_card_ge hKle (by rw [hstabcard, hK])).symm
  have hindex : (MulAction.stabilizer A F).index = 4 := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hFcard]
  have hBfix (a : A) : a • B = B := Subtype.ext (hBinv a)
  have hBorb : MulAction.orbit A B = {B} := by
    ext U
    constructor
    · rintro ⟨a, rfl⟩
      exact Set.mem_singleton_iff.mpr (hBfix a)
    · rintro (rfl : U = B)
      exact MulAction.mem_orbit_self _
  have hBcard : Nat.card (MulAction.orbit A B) = 1 := by rw [hBorb]; simp
  obtain ⟨U, hU⟩ := exists_moved_point ρ z f B F hB hF hcomm hinv
  have hzU : z • U ≠ U := fun he => hU (congrArg Subtype.val he)
  have hUlower : 8 ≤ Nat.card (MulAction.orbit A U) := by
    have hp := period_eight r U hr (by rwa [hrz])
    exact hp ▸ period_le_orbit r U
  have hdBF : Disjoint (MulAction.orbit A B) (MulAction.orbit A F) :=
    disjoint_orbits B F (by rwa [hBorb, Set.mem_singleton_iff])
  have hdBU : Disjoint (MulAction.orbit A B) (MulAction.orbit A U) :=
    disjoint_orbits B U (fun h => hzU (central_fixed_on_orbit z hzc B (hBfix z) U h))
  have hdFU : Disjoint (MulAction.orbit A F) (MulAction.orbit A U) :=
    disjoint_orbits F U (fun h => hzU (central_fixed_on_orbit z hzc F hzF U h))
  have hunion : (MulAction.orbit A B ∪ MulAction.orbit A F ∪
      MulAction.orbit A U).ncard = 1 + 4 + Nat.card (MulAction.orbit A U) := by
    rw [Set.ncard_union_eq (hdBU.union_left hdFU), Set.ncard_union_eq hdBF,
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      hBcard, hFcard]
  have htotal : Nat.card (OrderPoints 3 E) = 13 := OrderPoints.card_thirteen hE
  have hbound := Set.ncard_le_card (s := MulAction.orbit A B ∪ MulAction.orbit A F ∪
    MulAction.orbit A U)
  rw [hunion, htotal] at hbound
  have hUcard : Nat.card (MulAction.orbit A U) = 8 := by omega
  have hexhaust : MulAction.orbit A B ∪ MulAction.orbit A F ∪ MulAction.orbit A U =
      Set.univ := (Set.eq_univ_iff_ncard _).mpr (by rw [hunion, hUcard, htotal])
  exact ⟨hBorb, hBcard, hFcard, hstab, hindex, U, hUcard, hdBF, hdBU, hdFU, hexhaust⟩

end SemidihedralTernaryPoints
