module

public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.Representation.NonsplitFour

/-!
# Numerical endgame for odd Goldschmidt–O'Nan pairs

A nontrivial abelian kernel with fixed-point-free conjugation by the cyclic
actor gives the degree bound `|Y| ≤ dim V`. Once the fixed space is a line,
the cyclic order formula forces dimension three. Orbit-stabilizer and the
order of `GL₃(2)` then give order 21. Noncommutativity follows directly from
faithfulness and transitivity on nonzero vectors.

These are the terminal deductions in GLS, Number 2, Chapter C, Proposition
14.2 (`refs/KGroup/GLS2/ChapterC.tex`). The kernel and the one-dimensional
fixed-space assertion are explicit hypotheses here; their construction is
not asserted by this module.
-/

public section

open scoped IsMulCommutative
open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
namespace Representation.GoldschmidtONan
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

/-- A faithful transitive action cannot have both a nontrivial cyclic actor
and a nonzero vector fixed by that actor when the whole group is abelian. -/
theorem Input.not_commutative_of_nonzeroTransitive
    (h : Input ρ Y) (ht : NonzeroTransitive ρ) :
    ¬ ∀ x y : X, x * y = y * x := by
  intro hc
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.fixed_nontrivial
  apply h.nontrivial
  apply le_antisymm ?_ bot_le
  intro y hy
  apply Subgroup.mem_bot.mpr
  apply h.faithful
  ext w
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨x, rfl⟩ := ht v hv0 w hw
  have he : ρ y (ρ x v) = ρ x (ρ y v) := by
    simp only [← Module.End.mul_apply, ← map_mul, hc y x]
  simpa [show ρ y v = v from hv ⟨y, hy⟩] using he

/-- Transitivity makes the number of nonzero vectors divide the group order. -/
theorem NonzeroTransitive.card_nonzero_dvd [Finite X] [Finite V]
    (ht : NonzeroTransitive ρ) (v : V) (hv : v ≠ 0) : Nat.card V - 1 ∣ Nat.card X := by
  classical
  let : MulAction X V := {
    smul x w := ρ x w
    one_smul w := by change ρ 1 w = w; simp
    mul_smul x y w := by
      change ρ (x * y) w = ρ x (ρ y w)
      rw [map_mul, Module.End.mul_apply] }
  have horbit : MulAction.orbit X v = {w : V | w ≠ 0} := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩ he
      change ρ x v = 0 at he
      exact hv (action_injective x (by simpa using he))
    · exact ht v hv w
  have hc : Nat.card (MulAction.orbit X v) = Nat.card V - 1 := by
    rw [horbit]
    let := Fintype.ofFinite V
    let := Fintype.ofFinite {w : V // w ≠ 0}
    change Nat.card {w : V // w ≠ 0} = Nat.card V - 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      Nat.card_eq_fintype_card]
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup X v)
  rw [Nat.card_prod, hc] at he
  exact ⟨_, he.symm⟩

private theorem linear_lt_two_pow {m : ℕ} (hm : 3 ≤ m) : m + 2 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

/-- The Frobenius degree bound and a fixed line force dimension three. -/
theorem Input.dimension_eq_three_of_card_le [Finite X] [Finite V]
    (h : Input ρ Y) (hf : Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1)
    (hbound : Nat.card Y ≤ Module.finrank (ZMod 2) V) :
    Module.finrank (ZMod 2) V = 3 := by
  have hs := Submodule.finrank_add_eq_of_isCompl h.split
  rw [hf] at hs
  have hc := h.card_eq
  have hm := h.moved_dimension_gt_one
  have hup : Module.finrank (ZMod 2) (displacementSpan ρ Y ⊤) ≤ 2 := by
    by_contra hn
    have hp := linear_lt_two_pow (m := Module.finrank (ZMod 2) (displacementSpan ρ Y ⊤))
      (by omega)
    omega
  omega

/-- In dimension three, oddness and the two orbit lengths determine the order. -/
theorem Input.card_eq_twenty_one_of_dimension_eq_three [Finite X] [Finite V]
    (h : Input ρ Y) (ht : NonzeroTransitive ρ) (ho : Odd (Nat.card X))
    (hdim : Module.finrank (ZMod 2) V = 3) : Nat.card X = 21 := by
  have hdiv := Representation.card_dvd_card_GL_of_injective ρ h.faithful
  rw [hdim, Matrix.card_GL_field] at hdiv
  norm_num [Fin.prod_univ_succ] at hdiv
  have hdiv21 : Nat.card X ∣ 21 := by
    apply (ho.coprime_two_right.pow_right 3).dvd_of_dvd_mul_left
    norm_num
    exact hdiv
  have hcV : Nat.card V = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hdim]
    norm_num
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.fixed_nontrivial
  have h7 : 7 ∣ Nat.card X := by simpa [hcV] using ht.card_nonzero_dvd v hv0
  have hfpos : 0 < Module.finrank (ZMod 2) (fixedSpace ρ Y) := by
    let : Nontrivial (fixedSpace ρ Y) := Submodule.nontrivial_iff_ne_bot.mpr h.fixed_nontrivial
    exact Module.finrank_pos
  have hdm := h.moved_dimension_gt_one
  have hs := Submodule.finrank_add_eq_of_isCompl h.split
  have hd : Module.finrank (ZMod 2) (displacementSpan ρ Y ⊤) = 2 := by omega
  have h3 : 3 ∣ Nat.card X := by
    have hcY : Nat.card Y = 3 := by simpa [hd] using h.card_eq
    simpa [hcY] using Y.card_subgroup_dvd_card
  exact Nat.dvd_antisymm hdiv21 ((by decide : Nat.Coprime 3 7).mul_dvd_of_dvd_of_dvd h3 h7)

/-- A genuine abelian Frobenius kernel completes the numerical exceptional case. -/
theorem Input.exceptionalCase_of_abelian_kernel [Finite X] [Finite V]
    (h : Input ρ Y) (ht : NonzeroTransitive ρ) (ho : Odd (Nat.card X))
    (hf : Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1)
    (R : Subgroup X) [R.Normal] [IsMulCommutative R] (hR : R ≠ ⊥)
    (hfree : ∀ y : Y, y ≠ 1 → ∀ r : R, (y : X) * r * (y : X)⁻¹ = r → r = 1) :
    ExceptionalCase ρ Y := by
  let : Nontrivial R := R.nontrivial_iff_ne_bot.mpr hR
  have hoddR := Odd.of_dvd_nat ho R.card_subgroup_dvd_card
  have horder : (Nat.card R : ZMod 2) ≠ 0 := by
    obtain ⟨k, hk⟩ := hoddR
    rw [hk]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_add]
    exact one_ne_zero
  have hbound := Representation.card_le_finrank_of_fixedPointFree_normalizer_of_field
    ρ R Y h.faithful horder (by rw [R.normalizer_eq_top]; exact le_top) hfree
  have hdim := h.dimension_eq_three_of_card_le hf hbound
  exact ⟨hf, hdim, h.card_eq_twenty_one_of_dimension_eq_three ht ho hdim,
    h.not_commutative_of_nonzeroTransitive ht⟩

end Representation.GoldschmidtONan
