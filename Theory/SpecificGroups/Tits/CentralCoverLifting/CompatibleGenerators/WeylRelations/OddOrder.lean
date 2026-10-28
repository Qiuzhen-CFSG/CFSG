module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.Basic
import Mathlib.Tactic.Group

/-!
# Two normalized Weyl equations from odd powers

The VII(s₅) defect describes conjugation of the rotation r₁s₁ by s₅.
Reflection conjugation forces its square to be one; centrality of the fifth
power of the rotation also forces its fifth power to be one.

For VIII(s₄), the already normalized equation r₁s₂r₁=s₈ and IV(s₂,s₆)
imply that s₈ commutes with s₄, even though VII(s₄) is still only central.
Conjugating s₄ by r₈ and by r₈s₈ makes the VIII(s₄) defect have both
square and cube one. The same reflection argument gives square one for
the still unresolved global braid defect.

Source: Parrott (1972), §5, p.683, relations I, II, IV, VI–VIII; see
`refs/original/n-group-global/parrott-tits-presentation.md`.
Every result uses the literal auxiliary presentation and precisely `hroot`;
no exact Weyl equation or multiplier bound is assumed.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

private theorem sqinv {G : Type*} [Group G] {a : G} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

private theorem central_conj {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (a : G) : MulAut.conj a z = z := by
  simp only [MulAut.conj_apply]
  rw [Subgroup.mem_center_iff.mp hz a]
  group

private theorem central_dihedral_power_sq {G : Type*} [Group G]
    {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (n : ℕ)
    (hz : (a * b) ^ n ∈ Subgroup.center G) : ((a * b) ^ n) ^ 2 = 1 := by
  have hinv : MulAut.conj a (a * b) = (a * b)⁻¹ := by
    simp [MulAut.conj_apply, mul_inv_rev, sqinv ha, sqinv hb, ← mul_assoc,
      show a * a = 1 by simpa only [pow_two] using ha]
  have h : ((a * b) ^ n)⁻¹ = (a * b) ^ n := by
    rw [← inv_pow, ← hinv, ← map_pow, central_conj hz a]
  rw [pow_two]
  nth_rw 1 [← h]
  exact inv_mul_cancel _


private theorem central_twist_pow {G : Type*} [Group G]
    {a x z : G} (hz : z ∈ Subgroup.center G)
    (h : a * x = x * a * z) (n : ℕ) :
    a ^ n * x = x * a ^ n * z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      a ^ (n + 1) * x = a ^ n * (a * x) := by rw [pow_succ, mul_assoc]
      _ = (a ^ n * x) * a * z := by rw [h]; group
      _ = (x * a ^ n * z ^ n) * a * z := by rw [ih]
      _ = x * a ^ (n + 1) * z ^ (n + 1) := by
        rw [pow_succ, pow_succ]
        have hc := (Subgroup.mem_center_iff.mp ((Subgroup.center G).pow_mem hz n) a).symm
        simp only [mul_assoc]
        rw [← mul_assoc (z ^ n), hc]
        group

private theorem central_twist_order {G : Type*} [Group G]
    {a x z : G} (hz : z ∈ Subgroup.center G)
    (h : a * x = x * a * z) (n : ℕ)
    (hn : a ^ n ∈ Subgroup.center G) : z ^ n = 1 := by
  have hh := central_twist_pow hz h n
  rw [← Subgroup.mem_center_iff.mp hn x] at hh
  exact (mul_eq_left.mp hh.symm)

private theorem central_twist_dihedral {G : Type*} [Group G]
    {a b x z : G} (ha : a ^ 2 = 1)
    (hz : z ∈ Subgroup.center G) (h : a * x = x * a * z)
    (hb : Commute b x) (hc : (a * b) ^ 3 ∈ Subgroup.center G) : z = 1 := by
  have h2 : z ^ 2 = 1 := central_twist_order hz h 2 (by rw [ha]; exact one_mem _)
  have h3 : z ^ 3 = 1 := by
    apply central_twist_order hz (a := a * b) (x := x) _ 3 hc
    calc
      (a * b) * x = (a * x) * b := by rw [mul_assoc, hb.eq]; group
      _ = (x * a * z) * b := by rw [h]
      _ = x * (a * b) * z := by
        rw [mul_assoc, mul_assoc, ← Subgroup.mem_center_iff.mp hz b]
        group
  simpa only [pow_succ, h2, one_mul] using h3


private theorem central_rotation_defect {G : Type*} [Group G]
    {a b g z : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hbg : Commute b g) (hz : z ∈ Subgroup.center G)
    (hk : (a * b) ^ 5 ∈ Subgroup.center G)
    (h : a * g * a = (b * a) ^ 2 * g * z) : z = 1 := by
  let t := a * b
  have hr : MulAut.conj b t = t⁻¹ := by
    dsimp [t]
    simp only [mul_inv_rev, sqinv ha, sqinv hb]
    rw [mul_assoc, mul_assoc, show b * b = 1 by simpa only [pow_two] using hb, mul_one]
  have ht : MulAut.conj g t = t ^ 3 * z := by
    have hgz : g * z * g⁻¹ = z := central_conj hz g
    have hzb := (Subgroup.mem_center_iff.mp hz b).symm
    change g * (a * b) * g⁻¹ = (a * b) ^ 3 * z
    calc
      g * (a * b) * g⁻¹ = (g * a * g⁻¹) * b := by
        simp only [mul_assoc]
        rw [hbg.inv_right.eq]
      _ = a⁻¹ * ((b * a) ^ 2 * g * z) * g⁻¹ * b := by
        rw [← h]
        group
      _ = (a * b) ^ 3 * z := by
        rw [sqinv ha]
        calc
          _ = a * (b * a) ^ 2 * (g * z * g⁻¹) * b := by group
          _ = a * (b * a) ^ 2 * z * b := by rw [hgz]
          _ = a * (b * a) ^ 2 * b * z := by rw [mul_assoc, hzb]; group
          _ = _ := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hconj : MulAut.conj g (MulAut.conj b t) =
      MulAut.conj b (MulAut.conj g t) := by
    simp only [MulAut.conj_apply]
    have hgb := hbg.symm.eq
    have hgi := hbg.inv_inv.eq
    calc
      _ = (g * b) * t * (b⁻¹ * g⁻¹) := by group
      _ = (b * g) * t * (g⁻¹ * b⁻¹) := by rw [hgb, hgi]
      _ = _ := by group
  rw [hr, map_inv, ht, map_mul, map_pow, hr, central_conj hz b,
    mul_inv_rev, ← inv_pow] at hconj
  have hzcomm := (Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem hz)
    (t⁻¹ ^ 3)).symm
  rw [hzcomm] at hconj
  have hzi : z⁻¹ = z := mul_left_cancel hconj
  have h2 : z ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [← hzi]
    exact inv_mul_cancel _
  have hk2 : (t ^ 5) ^ 2 = 1 := central_dihedral_power_sq ha hb 5 hk
  have h5 : z ^ 5 = 1 := by
    have hp' : t ^ 5 = (t ^ 3 * z) ^ 5 := by
      rw [← ht, ← map_pow, central_conj hk g]
    rw [(show Commute (t ^ 3) z from Subgroup.mem_center_iff.mp hz _).mul_pow] at hp'
    have h15 : (t ^ 3) ^ 5 = t ^ 5 := by
      calc
        _ = (t ^ 5) ^ 2 * t ^ 5 := by group
        _ = t ^ 5 := by rw [hk2, one_mul]
    rw [h15] at hp'
    exact mul_eq_left.mp hp'.symm
  have h5' : z ^ 5 = z := by
    calc
      _ = (z ^ 2) ^ 2 * z := by group
      _ = z := by rw [h2]; simp
  exact h5'.symm.trans h5


private theorem source_commute {G : Type*} [Group G] {x y : G}
    (h : parrottCommutator x y = 1) : Commute x y := by
  have hh : ⁅x⁻¹, y⁻¹⁆ = 1 := by simpa only [parrottCommutator, commutatorElement_def, inv_inv] using h
  simpa only [inv_inv] using (commutatorElement_eq_one_iff_commute.mp hh).inv_inv

private theorem central_conjugate_commute {G : Type*} [Group G]
    {r x y u z : G} (hr : r ^ 2 = 1) (hz : z ∈ Subgroup.center G)
    (he : MulAut.conj r x = y * z) (hc : Commute u y) :
    Commute (MulAut.conj r u) x := by
  have hh := congrArg (MulAut.conj r) he
  rw [map_mul, central_conj hz r] at hh
  have hrr : r * r = 1 := by simpa only [pow_two] using hr
  have hd : MulAut.conj r (MulAut.conj r x) = x := by
    simp only [MulAut.conj_apply, sqinv hr]
    calc
      _ = (r * r) * x * (r * r) := by group
      _ = x := by rw [hrr]; simp
  rw [hd] at hh
  rw [hh]
  exact (hc.map (MulAut.conj r)).mul_right (hz.comm _).symm

variable (hroot : ∀ j, isPowerRootRelator j = true →
  FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
include hroot

private theorem vii_s2_relation :
    FreeGroup.lift normalizedGenerator (parrottRelator .vii_s2) = 1 := by
  simpa [correctionWord, hroot .i_r1 rfl, hroot .iii_s1_s7 rfl,
    hroot .v_s7_s4 rfl] using normalizedGenerator_correctionWord .s8

/-- The VII(s₅) central defect has both square and fifth power one, hence vanishes.
Only the prescribed power/root hypothesis is used. -/
theorem weyl_vii_s5_relation :
    FreeGroup.lift normalizedGenerator (parrottRelator .vii_s5) = 1 := by
  let a := normalizedGenerator .r1
  let b := normalizedGenerator .s1
  let g := normalizedGenerator .s5
  let z := FreeGroup.lift normalizedGenerator (parrottRelator .vii_s5)
  have ha : a ^ 2 = 1 := by simpa only [parrottRelator, map_pow,
    FreeGroup.lift_apply_of] using hroot .i_r1 rfl
  have hb : b ^ 2 = 1 := by simpa only [parrottRelator, map_pow,
    FreeGroup.lift_apply_of] using hroot .i_s1 rfl
  have hg : Commute b g := source_commute (by
    simpa only [parrottRelator, parrottCommutator, map_mul, map_inv,
      FreeGroup.lift_apply_of] using hroot .ii_s1_s5 rfl)
  have hz : z ∈ Subgroup.center NormalizedPresentation := normalizedGenerator_relators_central _
  have hk : (a * b) ^ 5 ∈ Subgroup.center NormalizedPresentation := by
    have hk' := (Subgroup.center NormalizedPresentation).inv_mem
      (normalizedGenerator_relators_central .vi_s1_r1)
    change ((b * a) ^ 5)⁻¹ ∈ Subgroup.center NormalizedPresentation at hk'
    simpa only [← inv_pow, mul_inv_rev, sqinv ha, sqinv hb] using hk'
  have he : a * g * a = (b * a) ^ 2 * g * z := by
    have hv : a * g * a * ((b * a) ^ 2 * g)⁻¹ = z := by
      simp only [z, parrottRelator, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
      rfl
    exact (mul_inv_eq_iff_eq_mul.mp hv).trans (hz.comm _).eq
  exact central_rotation_defect ha hb hg hz hk he

/-- Conjugating IV(s₂,s₆) by r₁ gives commutation of s₈ with s₄.
The central third-power relation then removes the VIII(s₄) defect. -/
theorem weyl_viii_s4_relation :
    FreeGroup.lift normalizedGenerator (parrottRelator .viii_s4) = 1 := by
  let r := normalizedGenerator .r1
  let a := normalizedGenerator .r8
  let b := normalizedGenerator .s8
  let x := normalizedGenerator .s4
  let y := normalizedGenerator .s6
  let u := normalizedGenerator .s2
  let z := FreeGroup.lift normalizedGenerator (parrottRelator .viii_s4)
  let c := FreeGroup.lift normalizedGenerator (parrottRelator .vii_s4)
  have hr : r ^ 2 = 1 := by simpa only [parrottRelator, map_pow,
    FreeGroup.lift_apply_of] using hroot .i_r1 rfl
  have ha : a ^ 2 = 1 := by simpa only [parrottRelator, map_pow,
    FreeGroup.lift_apply_of] using hroot .i_r8 rfl
  have hz : z ∈ Subgroup.center NormalizedPresentation := normalizedGenerator_relators_central _
  have hc : c ∈ Subgroup.center NormalizedPresentation := normalizedGenerator_relators_central _
  have hcuy : Commute u y := source_commute (by
    simpa only [parrottRelator, parrottCommutator, map_mul, map_inv,
      FreeGroup.lift_apply_of] using hroot .iv_s2_s6 rfl)
  have he : MulAut.conj r x = y * c := by
    have hv : r * x * r * y⁻¹ = c := by
      simp only [c, parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
      rfl
    simpa only [MulAut.conj_apply, sqinv hr] using
      (mul_inv_eq_iff_eq_mul.mp hv).trans (hc.comm _).eq
  have hu : MulAut.conj r u = b := by
    have hv : r * u * r * b⁻¹ = 1 := by
      simpa only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
        using vii_s2_relation hroot
    simpa only [MulAut.conj_apply, sqinv hr] using mul_inv_eq_one.mp hv
  have hbx : Commute b x := hu ▸ central_conjugate_commute hr hc he hcuy
  have hax : a * x = x * a * z := by
    have hv : a * x * a * x⁻¹ = z := by
      simp only [z, parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
      rfl
    have hv' : a * x * a = x * z :=
      (mul_inv_eq_iff_eq_mul.mp hv).trans (hz.comm _).eq
    have hh : a * x = x * z * a⁻¹ := by
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using
        congrArg (fun w => w * a⁻¹) hv'
    rw [sqinv ha] at hh
    rw [hh, mul_assoc, (hz.comm a).eq, ← mul_assoc]
  have hk : (a * b) ^ 3 ∈ Subgroup.center NormalizedPresentation := by
    simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of] using
      normalizedGenerator_relators_central .vi_r8_s8
  exact central_twist_dihedral ha hz hax hbx hk


/-- Centrality of the braid word and the two reflection squares already force
its defect to have square one. Vanishing of that defect remains separate. -/
theorem weyl_braid_defect_square :
    (FreeGroup.lift normalizedGenerator (parrottRelator .vi_r1_r8)) ^ 2 = 1 := by
  have ha : (normalizedGenerator .r1) ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using hroot .i_r1 rfl
  have hb : (normalizedGenerator .r8) ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using hroot .i_r8 rfl
  have hz : (normalizedGenerator .r1 * normalizedGenerator .r8) ^ 8 ∈
      Subgroup.center NormalizedPresentation := by
    simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of] using
      normalizedGenerator_relators_central .vi_r1_r8
  simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of] using
    central_dihedral_power_sq ha hb 8 hz

end Tits.CentralCoverLifting.CompatibleGenerators
