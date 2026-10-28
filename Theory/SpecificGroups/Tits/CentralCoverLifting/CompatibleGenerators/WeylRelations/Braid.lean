module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.OddOrder
import Mathlib.Tactic.Group

/-!
# Vanishing of the normalized Weyl braid defect

The correction identities recover VI(ii), VIII(s₁) and VIII(r₃) from the
power/root equations and the remaining conjugation seeds. VII(s₅) implies
that r₁ centralizes r₅ = s₁s₅²: conjugation by s₅ cubes r₁s₁, so conjugation
by s₅² inverts this rotation of fifth power one. The conjugation chain through
s₁, r₃, r₅ and s₇r₇ then gives
`conj ((r₁r₈)⁴) s₁ = conj r₁ s₁`.

Put q = r₁(r₁r₈)⁴ and c = (r₁r₈)⁸. The chain says q centralizes s₁, while
q conjugates r₁ to c⁻¹r₁. Centrality of c and (r₁s₁)⁵ = 1 force c⁵ = 1.
The already proved c² = 1 therefore gives c = 1.

Source: Parrott (1972), §5, p.683, relations I–VIII, and the fourth-power
conjugation calculation in §6, p.684; see
`refs/original/n-group-global/parrott-tits-presentation.md`. The chain is
proved here directly from the literal relators, retaining the source
commutator `a⁻¹ * b⁻¹ * a * b`. The centrality hypothesis comes from the
auxiliary normalized presentation. No ambient recognition hypotheses,
splitting theorem, or multiplier computation are used.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators

private theorem sqinv {G : Type*} [Group G] {a : G} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

private theorem tail {G : Type*} [Group G] {a b c : G}
    (h : a * b = c) (k : G) : a * (b * k) = c * k := by rw [← mul_assoc, h]

private theorem conj_involutive {G : Type*} [Group G] {a : G}
    (h : a ^ 2 = 1) : Function.Involutive (MulAut.conj a) := by
  intro x
  have haa : a * a = 1 := by simpa only [pow_two] using h
  simp only [MulAut.conj_apply, sqinv h, mul_assoc, tail haa, one_mul, haa, mul_one]

-- The square of the cubing automorphism inverts a rotation of fifth power one.
private theorem centralizes_r5 {G : Type*} [Group G] {a y x : G}
    (ha : a ^ 2 = 1) (hy : y ^ 2 = 1) (hyx : Commute y x)
    (h5 : (y * a) ^ 5 = 1) (hx : a * x * a = (y * a) ^ 2 * x) :
    MulAut.conj a (y * x ^ 2) = y * x ^ 2 := by
  let t := a * y
  have ht : MulAut.conj x t = t ^ 3 := by
    change x * (a * y) * x⁻¹ = (a * y) ^ 3
    calc
      _ = (x * a * x⁻¹) * y := by
        simp only [mul_assoc]
        rw [hyx.inv_right.eq]
      _ = a⁻¹ * ((y * a) ^ 2 * x) * x⁻¹ * y := by rw [← hx]; group
      _ = (a * y) ^ 3 := by
        rw [sqinv ha]
        simp only [pow_succ, pow_zero, one_mul]
        group
  have ht5 : t ^ 5 = 1 := by
    have hh := congrArg Inv.inv h5
    simpa only [← inv_pow, mul_inv_rev, sqinv ha, sqinv hy, inv_one] using hh
  have hx2 : MulAut.conj (x ^ 2) t = t⁻¹ := by
    calc
      _ = MulAut.conj x (MulAut.conj x t) := by
        simp only [MulAut.conj_apply, pow_two]; group
      _ = t ^ 9 := by rw [ht, map_pow, ht, ← pow_mul]
      _ = t⁻¹ := by
        apply mul_right_cancel (b := t)
        calc
          t ^ 9 * t = (t ^ 5) ^ 2 := by group
          _ = t⁻¹ * t := by rw [ht5]; simp
  have hyt : MulAut.conj y t = t⁻¹ := by
    simp only [t, MulAut.conj_apply, mul_inv_rev, sqinv ha, sqinv hy]
    simp only [mul_assoc, show y * y = 1 by simpa only [pow_two] using hy, mul_one]
  have hzt : MulAut.conj (y * x ^ 2) t = t := by
    calc
      _ = MulAut.conj y (MulAut.conj (x ^ 2) t) := by
        simp only [MulAut.conj_apply]; group
      _ = t := by rw [hx2, map_inv, hyt, inv_inv]
  have hzy : MulAut.conj (y * x ^ 2) y = y := by
    have hc : Commute (y * x ^ 2) y := (Commute.refl y).mul_left (hyx.pow_right 2).symm
    exact mul_inv_eq_iff_eq_mul.mpr hc.eq
  have hza : MulAut.conj (y * x ^ 2) a = a := by
    have hat : a = t * y := by
      simp only [t, mul_assoc, show y * y = 1 by simpa only [pow_two] using hy, mul_one]
    rw [hat, map_mul, hzt, hzy]
  have hc : Commute (y * x ^ 2) a := mul_inv_eq_iff_eq_mul.mp hza
  exact mul_inv_eq_iff_eq_mul.mpr hc.symm.eq

-- The four-step source calculation needs only the displayed conjugation equations.
private theorem fourth_conjugation {G : Type*} [Group G] {a b y t z u : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hat : MulAut.conj a t = u) (haz : MulAut.conj a z = z)
    (hbt : MulAut.conj b t = z) (hby : MulAut.conj b y = u) :
    MulAut.conj ((a * b) ^ 4) y = MulAut.conj a y := by
  have hau : MulAut.conj a u = t := by rw [← hat]; exact conj_involutive ha t
  have hbu : MulAut.conj b u = y := by rw [← hby]; exact conj_involutive hb y
  have hbz : MulAut.conj b z = t := by rw [← hbt]; exact conj_involutive hb t
  calc
    _ = MulAut.conj a (MulAut.conj b (MulAut.conj a (MulAut.conj b
        (MulAut.conj a (MulAut.conj b (MulAut.conj a (MulAut.conj b y))))))) := by
      simp only [MulAut.conj_apply, pow_succ, pow_zero]
      group
    _ = MulAut.conj a y := by rw [hby, hau, hbt, haz, hbz, hat, hbu]

-- Centrality turns the fourth-power calculation into an odd-power bound on the defect.
private theorem braid_of_fourth_conjugation {G : Type*} [Group G] {a b y : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (h5 : (a * y) ^ 5 = 1)
    (h4 : MulAut.conj ((a * b) ^ 4) y = MulAut.conj a y)
    (hz : (a * b) ^ 8 ∈ Subgroup.center G) (h2 : ((a * b) ^ 8) ^ 2 = 1) :
    (a * b) ^ 8 = 1 := by
  let w := a * b
  let q := a * w ^ 4
  let z := w ^ 8
  have hqw : MulAut.conj q y = y := by
    calc
      _ = MulAut.conj a (MulAut.conj (w ^ 4) y) := by
        simp only [q, MulAut.conj_apply]; group
      _ = y := by rw [h4]; exact conj_involutive ha y
  have haw : MulAut.conj a w = w⁻¹ := by
    simp only [w, MulAut.conj_apply, mul_inv_rev, sqinv ha, sqinv hb]
    have haa : a * a = 1 := by simpa only [pow_two] using ha
    simp only [← mul_assoc, haa, one_mul]
  have hqa : MulAut.conj q a = z⁻¹ * a := by
    calc
      _ = MulAut.conj a (w ^ 4) * w⁻¹ ^ 4 * a := by
        simp only [q, MulAut.conj_apply, mul_inv_rev, sqinv ha, inv_pow]
        group
      _ = z⁻¹ * a := by rw [map_pow, haw]; dsimp [z]; group
  have hqay : MulAut.conj q (a * y) = z⁻¹ * (a * y) := by
    rw [map_mul, hqa, hqw, mul_assoc]
  have hz5 : z ^ 5 = 1 := by
    have hh := congrArg (MulAut.conj q) h5
    rw [map_pow, map_one, hqay] at hh
    have hc : Commute z⁻¹ (a * y) := ((Subgroup.center G).inv_mem hz).comm _
    rw [hc.mul_pow, h5, mul_one, inv_pow, inv_eq_one] at hh
    exact hh
  have hz5' : z ^ 5 = z := by
    calc
      z ^ 5 = (z ^ 2) ^ 2 * z := by group
      _ = z := by rw [h2]; simp
  exact hz5'.symm.trans hz5

-- Recover only the three extra equations used below; the braid is never assumed.
private theorem needed_relations
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hconj : ∀ j, isRemainingWeylConjugation j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    FreeGroup.lift normalizedGenerator (parrottRelator .vi_s1_r1) = 1 ∧
    FreeGroup.lift normalizedGenerator (parrottRelator .viii_s1) = 1 ∧
    FreeGroup.lift normalizedGenerator (parrottRelator .viii_r3) = 1 := by
  have hvii5 := weyl_vii_s5_relation hroot
  have hviii4 := weyl_viii_s4_relation hroot
  have hviii7 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_s7) = 1 := by
    simpa [correctionWord, hroot .iii_s1_s8 rfl, hroot .v_s5_s4 rfl,
      hviii4] using normalizedGenerator_correctionWord .s1
  have hvi1 : FreeGroup.lift normalizedGenerator (parrottRelator .vi_s1_r1) = 1 := by
    simpa [correctionWord, hroot .i_r1 rfl, hroot .i_r8 rfl, hroot .iii_s1_s8 rfl,
      hroot .v_s5_s4 rfl, hvii5, hviii7] using normalizedGenerator_correctionWord .r1
  have hviii3 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_s3) = 1 := by
    simpa [correctionWord, hroot .i_s1 rfl, hroot .v_s5_s4 rfl,
      hconj .vii_s3 rfl, hviii4] using normalizedGenerator_correctionWord .s3
  have hviii1 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_s1) = 1 := by
    simpa [correctionWord, hroot .iii_s1_s8 rfl, hroot .v_s5_s4 rfl,
      hvii5, hconj .vii_s3 rfl, hviii4, hviii3] using normalizedGenerator_correctionWord .s5
  have hviiir3 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_r3) = 1 := by
    simpa [correctionWord, hroot .i_r1 rfl, hconj .vii_r3 rfl,
      hviii1, hviii7, hviii3] using normalizedGenerator_correctionWord .s7
  exact ⟨hvi1, hviii1, hviiir3⟩

/-- The power/root equations and remaining Weyl conjugations kill the literal
VI(i) defect in the normalized presentation. This supplies the braid premise
of `weyl_seed_relations_of_remaining` and its all-37-relations consumer. -/
theorem weyl_braid_relation_of_remaining
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hconj : ∀ j, isRemainingWeylConjugation j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    FreeGroup.lift normalizedGenerator (parrottRelator .vi_r1_r8) = 1 := by
  let a := normalizedGenerator .r1
  let b := normalizedGenerator .r8
  let y := normalizedGenerator .s1
  let x := normalizedGenerator .s5
  let t := FreeGroup.lift normalizedGenerator parrottR3
  let z := FreeGroup.lift normalizedGenerator parrottR5
  let u := normalizedGenerator .s7 * FreeGroup.lift normalizedGenerator parrottR7
  obtain ⟨hvi1, hviii1, hviiir3⟩ := needed_relations hroot hconj
  have ha : a ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using hroot .i_r1 rfl
  have hb : b ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using hroot .i_r8 rfl
  have hy : y ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using hroot .i_s1 rfl
  have hyx : Commute y x := by
    have hh : y⁻¹ * x⁻¹ * y * x = 1 := by
      simpa only [parrottRelator, parrottCommutator, map_mul, map_inv,
        FreeGroup.lift_apply_of] using hroot .ii_s1_s5 rfl
    apply mul_left_cancel (a := x⁻¹)
    calc
      x⁻¹ * (y * x) = y * (y⁻¹ * x⁻¹ * y * x) := by group
      _ = x⁻¹ * (x * y) := by rw [hh]; group
  have h5 : (y * a) ^ 5 = 1 := by
    simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of] using hvi1
  have hx : a * x * a = (y * a) ^ 2 * x := by
    apply mul_inv_eq_one.mp
    simpa only [parrottRelator, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
      using weyl_vii_s5_relation hroot
  have haz : MulAut.conj a z = z := centralizes_r5 ha hy hyx h5 hx
  have hat : MulAut.conj a t = u := by
    have hh : a * t * a * u⁻¹ = 1 := by
      simpa only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
        using hconj .vii_r3 rfl
    simpa only [MulAut.conj_apply, sqinv ha] using mul_inv_eq_one.mp hh
  have hbt : MulAut.conj b t = z := by
    have hh : b * t * b * z⁻¹ = 1 := by
      simpa only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of] using hviiir3
    simpa only [MulAut.conj_apply, sqinv hb] using mul_inv_eq_one.mp hh
  have hby : MulAut.conj b y = u := by
    have hh : b * y * b * u⁻¹ = 1 := by
      simpa only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of] using hviii1
    simpa only [MulAut.conj_apply, sqinv hb] using mul_inv_eq_one.mp hh
  have h5' : (a * y) ^ 5 = 1 := by
    have hh := congrArg Inv.inv h5
    simpa only [← inv_pow, mul_inv_rev, sqinv ha, sqinv hy, inv_one] using hh
  have hcentral : (a * b) ^ 8 ∈ Subgroup.center NormalizedPresentation := by
    simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of]
      using normalizedGenerator_relators_central .vi_r1_r8
  have hsquare : ((a * b) ^ 8) ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of]
      using weyl_braid_defect_square hroot
  have h := braid_of_fourth_conjugation ha hb h5'
    (fourth_conjugation ha hb hat haz hbt hby) hcentral hsquare
  simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of] using h

end Tits.CentralCoverLifting.CompatibleGenerators
