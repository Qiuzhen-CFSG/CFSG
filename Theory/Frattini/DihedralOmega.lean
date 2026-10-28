module

public import Theory.Frattini.OmegaProducts
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.LinearCombination

/-!
# Frattini omega of dihedral two-groups

In a dihedral group with rotation order at least four, the Frattini subgroup
lies in the rotations. Its elements of square one are central. Conversely the
central half-turn is the square of a quarter-turn and hence belongs to the
Frattini subgroup. Thus its first omega is the center; the whole Frattini
subgroup is not in general the center.

The rotation calculations follow the intrinsic dihedral presentation in
Mathlib. This is the factor calculation used by Aschbacher–Smith, printed
p.1182 / PDF p.1199, after Lemma 16.3.12.
-/

@[expose] public section
namespace DihedralFrattini

open Subgroup
open scoped commutatorElement

private lemma rotation_mem {m : ℕ} [NeZero m] (i : ZMod m) :
    DihedralGroup.r i ∈ zpowers (DihedralGroup.r (1 : ZMod m)) := by
  have h := pow_mem (mem_zpowers (DihedralGroup.r (1 : ZMod m))) i.val
  simpa only [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] using h

private lemma center_rotation {m : ℕ} (hm : 2 < m)
    (z : DihedralGroup m) (hz : z ∈ center (DihedralGroup m)) :
    z ∈ zpowers (DihedralGroup.r (1 : ZMod m)) := by
  let : NeZero m := ⟨by omega⟩
  cases z with
  | r i => exact rotation_mem i
  | sr i =>
    have hi : i - 1 = i + 1 := DihedralGroup.sr.inj (mem_center_iff.mp hz (DihedralGroup.r 1))
    have htwo : (2 : ZMod m) = 0 := by linear_combination -hi
    have hv := congrArg ZMod.val htwo
    have hval : ZMod.val (2 : ZMod m) = 2 := ZMod.val_natCast_of_lt hm
    rw [hval, ZMod.val_zero] at hv
    omega

private lemma square_rotation {m : ℕ} [NeZero m] (x : DihedralGroup m) :
    x ^ 2 ∈ zpowers (DihedralGroup.r (1 : ZMod m)) := by
  cases x with
  | r i => exact pow_mem (rotation_mem i) 2
  | sr i => simp only [pow_two, DihedralGroup.sr_mul_self, one_mem]

private lemma commutator_rotation {m : ℕ} [NeZero m] (x y : DihedralGroup m) :
    ⁅x, y⁆ ∈ zpowers (DihedralGroup.r (1 : ZMod m)) := by
  rcases x with i | i <;> rcases y with j | j
  · simp only [commutatorElement_def, DihedralGroup.inv_r, DihedralGroup.r_mul_r]
    simp
  · simp only [commutatorElement_def, DihedralGroup.inv_r, DihedralGroup.inv_sr]
    exact rotation_mem _
  · simp only [commutatorElement_def, DihedralGroup.inv_sr, DihedralGroup.inv_r,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    exact rotation_mem _
  · simp only [commutatorElement_def, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]
    exact rotation_mem _

private lemma center_index_two_pow {n : ℕ} (hn : 2 ≤ n) {i : ZMod (2 ^ n)}
    (hi : (2 : ZMod (2 ^ n)) * i = 0) :
    i = 0 ∨ i = (2 ^ (n - 1) : ℕ) := by
  have hpow : 0 < 2 ^ n := by positivity
  have hlt : i.val < 2 ^ n := ZMod.val_lt i
  have h2 : 2 < 2 ^ n := by
    have hp : 4 ≤ 2 ^ n := by
      simpa using (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hn)
    omega

  have hv := congrArg ZMod.val hi
  rw [ZMod.val_zero, ZMod.val_mul] at hv
  have htwo : ZMod.val (2 : ZMod (2 ^ n)) = 2 :=
    ZMod.val_natCast_of_lt (by
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
      omega)
  rw [htwo] at hv
  have hmod : (2 * i.val) % (2 ^ n) = 0 := by
    simpa [Nat.mod_eq_of_lt h2] using hv
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hklt : k < 2 := by
    by_contra hnot
    have hk2 : 2 ≤ k := by omega
    have : 2 * (2 ^ n) ≤ 2 * i.val := by
      rw [hk]
      nlinarith
    nlinarith
  have hkcases : k = 0 ∨ k = 1 := by omega
  rcases hkcases with rfl | rfl
  · left
    apply (ZMod.val_eq_zero _).mp
    omega
  · right
    have hi' : i = (i.val : ZMod (2 ^ n)) := (ZMod.natCast_zmod_val i).symm
    rw [hi']
    congr 1
    have hpow' : 2 * 2 ^ (n - 1) = 2 ^ n := by
      calc
        2 * 2 ^ (n - 1) = 2 ^ (n - 1) * 2 := by ring
        _ = 2 ^ (n - 1 + 1) := by rw [pow_succ]
        _ = 2 ^ n := by congr 1; omega
    omega

lemma dihedral_isPGroup (n : ℕ) : IsPGroup 2 (DihedralGroup (2 ^ n)) := by
  apply IsPGroup.of_card (n := n + 1)
  rw [DihedralGroup.nat_card]
  rw [show 2 * 2 ^ n = 2 ^ (n + 1) by rw [pow_succ]; ring]

private lemma frattini_le_rotation {n : ℕ} (_hn : 2 ≤ n) :
    frattini (DihedralGroup (2 ^ n)) ≤ zpowers (DihedralGroup.r (1 : ZMod (2 ^ n))) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (IsPGroup 2 (DihedralGroup (2 ^ n))) := ⟨dihedral_isPGroup n⟩
  let q : DihedralGroup (2 ^ n) := DihedralGroup.r 1
  have hcomm : (_root_.commutator (DihedralGroup (2 ^ n)) : Subgroup _) ≤ zpowers q := by
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    exact commutator_rotation a b
  rw [frattini_eq_closure_commutator_union_powers (p := 2)]
  apply (closure_le (zpowers q)).2
  intro x hx
  rcases hx with hx | ⟨y, rfl⟩
  · exact hcomm hx
  · exact square_rotation y

private lemma half_twice {n : ℕ} (hn : 1 ≤ n) :
    ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) * 2 = 0 := by
  have hp : 2 ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hc := congrArg (fun a : ℕ => (a : ZMod (2 ^ n))) hp
  rw [ZMod.natCast_self] at hc
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc

lemma half_square {n : ℕ} (hn : 1 ≤ n) :
    (DihedralGroup.r ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))) ^ 2 = 1 := by
  rw [DihedralGroup.r_pow]
  change DihedralGroup.r (((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) * 2) = 1
  rw [half_twice hn, DihedralGroup.r_zero]

private lemma rotation_square_center {m : ℕ} {i : ZMod m}
    (hi : (DihedralGroup.r i) ^ 2 = 1) :
    DihedralGroup.r i ∈ center (DihedralGroup m) := by
  have he : i + i = 0 := DihedralGroup.r.inj (by simpa only [pow_two,
    DihedralGroup.r_mul_r, DihedralGroup.one_def] using hi)
  have hneg : -i = i := neg_eq_iff_add_eq_zero.mpr he
  apply mem_center_iff.mpr
  rintro (j | j)
  · simp only [DihedralGroup.r_mul_r, add_comm]
  · simp only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, sub_eq_add_neg, hneg]

private lemma rotation_involution_center {m : ℕ} {x : DihedralGroup m}
    (hx : x ∈ zpowers (DihedralGroup.r 1)) (hx2 : x ^ 2 = 1) :
    x ∈ center (DihedralGroup m) := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [DihedralGroup.r_one_zpow] at hx2 ⊢
  exact rotation_square_center hx2

lemma center_eq_half {n : ℕ} (hn : 2 ≤ n) :
    center (DihedralGroup (2 ^ n)) =
      zpowers (DihedralGroup.r ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))) := by
  apply le_antisymm
  · intro x hx
    have hm : 2 < 2 ^ n := by
      have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
      norm_num at hp
      omega
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (center_rotation hm x hx)
    rw [DihedralGroup.r_one_zpow] at hk
    subst x
    have hc := DihedralGroup.sr.inj (mem_center_iff.mp hx (DihedralGroup.sr 0))
    have hi : (2 : ZMod (2 ^ n)) * (k : ZMod (2 ^ n)) = 0 := by
      simp only [zero_add, zero_sub] at hc
      linear_combination hc
    rcases center_index_two_pow hn hi with h | h
    · simp [h]
    · rw [h]
      exact mem_zpowers _
  · exact zpowers_le.mpr (rotation_square_center (half_square (by omega)))

private lemma half_mem_frattini {n : ℕ} (hn : 2 ≤ n) :
    DihedralGroup.r ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈
      frattini (DihedralGroup (2 ^ n)) := by
  let : Fact (IsPGroup 2 (DihedralGroup (2 ^ n))) := ⟨dihedral_isPGroup n⟩
  have hp : 2 ^ (n - 2) * 2 = 2 ^ (n - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  have hs : (DihedralGroup.r ((2 ^ (n - 2) : ℕ) : ZMod (2 ^ n))) ^ 2 =
      DihedralGroup.r ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) := by
    rw [DihedralGroup.r_pow]
    congr 1
    simpa only [Nat.cast_mul] using congrArg (fun a : ℕ => (a : ZMod (2 ^ n))) hp
  rw [← hs]
  exact pth_power_mem_frattini_of_isPGroup (p := 2) _

lemma omega_frattini_dihedral {n : ℕ} (hn : 2 ≤ n) :
    omegaOneAmbient (frattini (DihedralGroup (2 ^ n))) = center (DihedralGroup (2 ^ n)) := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    exact rotation_involution_center (frattini_le_rotation hn hx) hx2
  · rw [center_eq_half hn]
    apply zpowers_le.mpr
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl _ (half_mem_frattini hn)
      (half_square (by omega))

/-- Isomorphism-invariant intrinsic form of the dihedral calculation. -/
theorem omegaFrattini_top_of_equiv {A : Type*} [Group A] {n : ℕ}
    (hn : 2 ≤ n) (e : A ≃* DihedralGroup (2 ^ n)) :
    (⊤ : Subgroup A).omegaFrattini = center A := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.omegaFrattini_top_map_equiv e, Subgroup.center_map_equiv e,
    Subgroup.omegaFrattini_top, omega_frattini_dihedral hn]

open DihedralGroup

private lemma even_rotation_mem {m : ℕ} [NeZero m] (i : ZMod m) :
    r (2 * i) ∈ zpowers (r (2 : ZMod m)) := by
  refine mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
  rw [r_zpow]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

private lemma square_even {m : ℕ} [NeZero m] (x : DihedralGroup m) :
    x ^ 2 ∈ zpowers (r (2 : ZMod m)) := by
  cases x with
  | r i => simpa only [r_pow, Nat.cast_ofNat, mul_comm] using even_rotation_mem i
  | sr i => simp only [pow_two, sr_mul_self, one_mem]

private lemma commutator_even {m : ℕ} [NeZero m] (x y : DihedralGroup m) :
    ⁅x, y⁆ ∈ zpowers (r (2 : ZMod m)) := by
  rcases x with i | i <;> rcases y with j | j
  · simp [commutatorElement_def]
  · have h := even_rotation_mem (m := m) i
    convert h using 1; simp only [commutatorElement_def, inv_r, inv_sr,
      r_mul_sr, sr_mul_r, sr_mul_sr]
    congr 1
    ring
  · have h := even_rotation_mem (m := m) (-j)
    convert h using 1; simp only [commutatorElement_def, inv_r, inv_sr,
      r_mul_r, sr_mul_r, sr_mul_sr]
    congr 1
    ring
  · have h := even_rotation_mem (m := m) (j - i)
    convert h using 1; simp only [commutatorElement_def, inv_sr,
      r_mul_sr, sr_mul_sr]
    congr 1
    ring

/-- The entire Frattini subgroup consists of the even rotations. -/
theorem frattini_eq_zpowers_two (n : ℕ) : frattini (DihedralGroup (2 ^ n)) =
    zpowers (r (2 : ZMod (2 ^ n))) := by
  let : Fact (IsPGroup 2 (DihedralGroup (2 ^ n))) := ⟨dihedral_isPGroup n⟩
  apply le_antisymm
  · rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    apply (closure_le _).mpr
    rintro x (hx | ⟨y, rfl⟩)
    · exact (Subgroup.commutator_le.mpr (fun a _ b _ => commutator_even a b)) hx
    · exact square_even y
  · apply zpowers_le.mpr
    have h := pth_power_mem_frattini_of_isPGroup (p := 2) (r (1 : ZMod (2 ^ n)))
    simpa only [r_one_pow, Nat.cast_ofNat] using h

/-- Only for the order-eight factor does the whole Frattini equal the center. -/
theorem frattini_eq_center_of_equiv_four {A : Type*} [Group A]
    (e : A ≃* DihedralGroup 4) : frattini A = center A := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.frattini_map_equiv e, Subgroup.center_map_equiv e]
  exact (frattini_eq_zpowers_two 2).trans (by
    simpa only [Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat] using
      (center_eq_half (n := 2) (by omega)).symm)

end DihedralFrattini
