module

public import Theory.SpecificGroups.Triality.LeviFields
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nontrivial parameters for the folded triality torus

The product x F(x) F²(x) belongs to the actual Frobenius fixed field.
A generator of GF(q³)ˣ cannot have norm one when q > 2: its order q³ - 1
would divide the strictly smaller positive integer 1 + q + q².
The fixed field likewise has a nonidentity unit since its order is q > 2.
These witnesses supply the torus weights used by the radical commutator proof.

Source: the coefficient fields and Cartan parameters of GLS3 2.4.1 and
2.4.7 (`refs/KGroup/GLS3/chapter2.tex`), in the triality case of
Aschbacher–Smith F.1.12(II), printed pp.263–264 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates.LeviCommutators
/-- The three Frobenius factors of the norm, in the actual fixed field. -/
def cubicNorm (P : Parameters) (x : ExtensionField P) : fixedField P :=
  ⟨x * fieldFrobenius P x * fieldFrobenius P (fieldFrobenius P x), by
    change fieldFrobenius P _ = _
    simp only [map_mul, fieldFrobenius_three]
    ring⟩


/-- A field of order greater than two has a nonidentity unit. -/
theorem exists_fixedUnit_ne_one (P : Parameters) (hq : 2 < P.q) :
    ∃ t : (fixedField P)ˣ, t.val ≠ 1 := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (fixedField P)ˣ)
  refine ⟨t, ?_⟩
  intro he
  have ht1 : t = 1 := Units.ext he
  rw [ht1, orderOf_one, Nat.card_units, card_fixedField] at ht
  omega

/-- A generator of the cubic field units has nonidentity norm when q > 2. -/
theorem exists_cubicNorm_ne_one (P : Parameters) (hq : 2 < P.q) :
    ∃ t : (ExtensionField P)ˣ, cubicNorm P t.val ≠ 1 := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ExtensionField P)ˣ)
  refine ⟨t, ?_⟩
  intro he
  have hpow : t ^ (1 + P.q + P.q ^ 2) = 1 := by
    apply Units.ext
    have hv := congrArg (fun x : fixedField P => x.val) he
    change t.val * fieldFrobenius P t.val *
      fieldFrobenius P (fieldFrobenius P t.val) = 1 at hv
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    simpa only [fieldFrobenius_apply, ← pow_mul, pow_two, pow_add, pow_one] using hv
  have hd := orderOf_dvd_of_pow_eq_one hpow
  rw [ht, Nat.card_units, card_extensionField] at hd
  have hb := Nat.le_of_dvd (by omega : 0 < 1 + P.q + P.q ^ 2) hd
  have hsmall : 1 + P.q + P.q ^ 2 < P.q ^ 3 - 1 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (show 3 ≤ P.q by omega)
    have hc : 1 + P.q + P.q ^ 2 + 1 < P.q ^ 3 := by
      rw [hn]
      nlinarith
    omega
  omega
end Triality.Standard.RadicalCoordinates.LeviCommutators
