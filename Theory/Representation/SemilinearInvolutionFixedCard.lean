module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Fixed cardinalities of semilinear involutions in characteristic two

A nonidentity involutory field automorphism admits a scalar of trace one.
For an involutive semilinear additive actor, multiplying a fixed vector by this
scalar expresses that vector as a displacement. Thus the displacement map has
both kernel and image equal to the fixed subgroup; its cardinality formula gives
the square-root count. The argument needs neither a chosen basis nor a separate
descent theorem.

The multiplicative and marked-equivalence interfaces supply the fixed-count
premises for the elementary-layer involution-fusion argument. In particular,
they apply to the literal actions on O₂(H) and J(S)/O₂(H), after identifying
those actions with their semilinear models.

Source: Aschbacher–Smith, Lemma 2.4.12(2), printed p.532, manuscript of
1 March 2004; the underlying scalar calculation is additive Hilbert 90.
-/

public section

namespace Representation.SemilinearInvolution
variable {F V : Type*} [Field F] [CharP F 2]
  [AddCommGroup V] [Module F V]

/-- A nontrivial semilinear involution has square-root fixed cardinality. -/
theorem fixed_card_sq (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (hσne : σ ≠ RingEquiv.refl F)
    (T : V →+ V) (hT : Function.Involutive T)
    (hsemi : ∀ (a : F) (v : V), T (a • v) = σ a • T v) :
    Nat.card (T.eqLocus (AddMonoidHom.id V)) ^ 2 = Nat.card V := by
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    apply hσne
    ext a
    exact not_not.mp (not_exists.mp h a)
  have hd : a + σ a ≠ 0 := by
    intro h
    apply ha
    calc
      σ a = a + (a + σ a) := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      _ = a := by rw [h, add_zero]
  let t := a / (a + σ a)
  have ht : t + σ t = 1 := by
    dsimp [t]
    rw [map_div₀, map_add, hσ, add_comm (σ a), ← add_div, div_self hd]
  have hvneg (v : V) : -v = v := by
    apply neg_eq_of_add_eq_zero_left
    calc
      v + v = ((1 : F) + 1) • v := by rw [add_smul, one_smul]
      _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
  let δ : V →+ V := T - AddMonoidHom.id V
  have hk : δ.ker = T.eqLocus (AddMonoidHom.id V) := by
    ext v
    change T v - v = 0 ↔ T v = v
    exact sub_eq_zero
  have hr : δ.range = δ.ker := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      change T (T w - w) - (T w - w) = 0
      rw [sub_eq_zero, map_sub, hT]
      simp only [sub_eq_add_neg, hvneg, add_comm]
    · intro hv
      have hv' : T v = v := by
        change v ∈ T.eqLocus (AddMonoidHom.id V)
        rwa [← hk]
      refine ⟨t • v, ?_⟩
      change T (t • v) - t • v = v
      rw [hsemi, hv', sub_eq_add_neg, hvneg, ← add_smul, add_comm (σ t), ht, one_smul]
  have hc := δ.ker.card_mul_index
  rw [AddSubgroup.index_ker, hr, hk, ← pow_two] at hc
  exact hc

/-- The same count in the multiplicative notation used for elementary groups. -/
theorem multiplicative_fixed_card_sq (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (hσne : σ ≠ RingEquiv.refl F)
    (T : V →+ V) (hT : Function.Involutive T)
    (hsemi : ∀ (a : F) (v : V), T (a • v) = σ a • T v) :
    Nat.card (T.toMultiplicative.eqLocus (MonoidHom.id (Multiplicative V))) ^ 2 =
      Nat.card (Multiplicative V) := by
  exact fixed_card_sq σ hσ hσne T hT hsemi

/-- Transfer the count to the literal fixed subgroup of a marked group action.
The intertwining identity identifies the actual actor with its semilinear model. -/
theorem fixed_card_sq_of_mulEquiv {A : Type*} [Group A]
    (σ : F ≃+* F) (hσ : Function.Involutive σ) (hσne : σ ≠ RingEquiv.refl F)
    (T : V →+ V) (hT : Function.Involutive T)
    (hsemi : ∀ (a : F) (v : V), T (a • v) = σ a • T v)
    (α : A →* A) (e : A ≃* Multiplicative V)
    (he : ∀ a : A, (e (α a)).toAdd = T (e a).toAdd) :
    Nat.card (α.eqLocus (MonoidHom.id A)) ^ 2 = Nat.card A := by
  let eV : A ≃ V := e.toEquiv.trans Multiplicative.toAdd
  have hfix (a : A) : α a = a ↔ T (eV a) = eV a := by
    change α a = a ↔ T (e a).toAdd = (e a).toAdd
    rw [← he]
    exact (Multiplicative.toAdd.injective.comp e.injective).eq_iff.symm
  let ef : α.eqLocus (MonoidHom.id A) ≃ T.eqLocus (AddMonoidHom.id V) :=
    eV.subtypeEquiv hfix
  calc
    Nat.card (α.eqLocus (MonoidHom.id A)) ^ 2 =
        Nat.card (T.eqLocus (AddMonoidHom.id V)) ^ 2 := by rw [Nat.card_congr ef]
    _ = Nat.card V := fixed_card_sq σ hσ hσne T hT hsemi
    _ = Nat.card A := (Nat.card_congr eV).symm
end Representation.SemilinearInvolution
