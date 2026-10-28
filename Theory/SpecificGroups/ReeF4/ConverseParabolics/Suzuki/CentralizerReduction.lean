module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.LeviRetraction
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Full Suzuki Levi action and the radical centralizer

If an element of the parabolic centralizes the radical, its Levi factor acts
on the radical as conjugation by an element of the radical. This action is
trivial modulo the radical's own commutator subgroup. Thus faithful action of
the full Levi on the radical abelianization implies self-centralization.

This is a conditional reduction. The full-Levi action, including the
complementary torus, must still be calculated; self-centralization in the
smaller seed is not an input that discharges that calculation.

Source: GLS3, Theorem 2.6.5(e,g), `refs/KGroup/GLS3/chapter2.tex`, and the
Suzuki local factor in Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

@[expose] public noncomputable section

namespace ReeF4.ConverseParabolics.SuzukiLevi

open Subgroup
open scoped commutatorElement

/-- Trivial conjugation on the actual radical modulo its own commutator subgroup. -/
def ActsTriviallyOnRadicalAbelianization (m : ℕ) (g : Model m) : Prop :=
  ∀ q ∈ radical m .suzuki, ⁅g, q⁆ ∈ ⁅radical m .suzuki, radical m .suzuki⁆

private theorem levi_factor_actsTrivially (m : ℕ) (r l : Model m)
    (hr : r ∈ radical m .suzuki)
    (hc : ∀ q ∈ radical m .suzuki, (r * l) * q = q * (r * l)) :
    ActsTriviallyOnRadicalAbelianization m l := by
  intro q hq
  have he : l * q * l⁻¹ = r⁻¹ * q * r := by
    calc
      l * q * l⁻¹ = r⁻¹ * ((r * l) * q) * l⁻¹ := by group
      _ = r⁻¹ * (q * (r * l)) * l⁻¹ := by rw [hc q hq]
      _ = r⁻¹ * q * r := by group
  have hcomm : ⁅l, q⁆ = ⁅r⁻¹, q⁆ := by
    simp only [commutatorElement_def, inv_inv]
    rw [he]
  rw [hcomm]
  exact commutator_mem_commutator (inv_mem hr) hq

/-- Faithful action of the entire Levi suffices for the full-parabolic centralizer. -/
theorem centralizer_le_radical_of_faithful_fullLevi (m : ℕ)
    (hfaithful : ∀ l ∈ fullLevi m,
      ActsTriviallyOnRadicalAbelianization m l → l = 1) :
    centralizer (intrinsicRadical m .suzuki : Set (parabolic m .suzuki)) ≤
      intrinsicRadical m .suzuki := by
  intro x hx
  obtain ⟨r, hr, l, hl, he⟩ := exists_radical_fullLevi_factors m x.val
    (by simpa only [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic]
      using x.property)
  have hr' : r ∈ radical m .suzuki := by rwa [suzuki_radical_eq_rootRadical]
  have hc : ∀ q ∈ radical m .suzuki, (r * l) * q = q * (r * l) := by
    intro q hq
    have h := mem_centralizer_iff.mp hx
      (⟨q, radical_le_parabolic m .suzuki hq⟩ : parabolic m .suzuki) hq
    have hval := congrArg Subtype.val h
    change q * x.val = x.val * q at hval
    simpa only [he] using hval.symm
  have hl1 := hfaithful l hl (levi_factor_actsTrivially m r l hr' hc)
  have hxval : x.val = r := by simpa only [hl1, mul_one] using he.symm
  change x.val ∈ radical m .suzuki
  rwa [hxval]

end ReeF4.ConverseParabolics.SuzukiLevi
