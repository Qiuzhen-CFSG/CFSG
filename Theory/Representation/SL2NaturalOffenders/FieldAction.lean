module

public import Theory.Representation.SL2NaturalOffenders.FieldAction.Kernel

/-!
# Binary semilinear offenders act linearly over the field

Let a finite group act faithfully and semilinearly on the two-dimensional
space over a finite binary field of order greater than two. Every elementary
abelian offender has trivial coefficient action.

The coefficient image has order at most two. If its kernel is trivial, the
actor order is at most two and a nontrivial coefficient automorphism bounds
the fixed-space order by the field order. If the kernel is nontrivial, the
transvection centralizer calculation bounds the kernel order times the
fixed-space order by the field order. In both cases a nontrivial coefficient
action gives `|A| * |C_V(A)| ≤ 2 * |F| < |F|²`, contradicting the offender
inequality.

This is the intrinsic finite-field estimate needed in the natural-module
case of Aschbacher--Smith, *The Classification of Quasithin Groups*,
B.4.2(1), printed p.86 of the combined manuscript (1 March 2004), and used
in C.2.7. Semilinearity is an explicit input; the parent natural-SL₂ theorem
constructs it from its normal natural-action hypotheses and retains the
final Sylow assembly.
-/

public section

namespace Representation.SL2NaturalOffenders
open Representation.BinaryOffender
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H] [Finite H]

/-- A faithful binary semilinear offender on `F²` acts linearly over `F` when
the finite field has more than two elements. -/
theorem offender_fieldLinear (hF : 2 < Nat.card F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hsemi : ∀ h : H, ∃ σ : F ≃+* F,
      ∀ (c : F) (v : Fin 2 → F), ρ h (c • v) = σ c • ρ h v)
    {A : Subgroup H} (hA : IsOffender ρ A) :
    ∀ a ∈ A, ∀ (c : F) (v : Fin 2 → F), ρ a (c • v) = c • ρ a v := by
  let φ : A →* (F ≃+* F) := (fieldAction ρ hsemi).comp A.subtype
  have hφ (a : A) (c : F) (v : Fin 2 → F) :
      ρ a (c • v) = φ a c • ρ a v := fieldAction_smul ρ hsemi a c v
  have htrivial (a : A) : φ a = 1 := by
    by_contra ha
    have hcard := card_le_two_mul_fieldAction_ker A hA.1.2 φ
    have hbound : Nat.card A * Nat.card (fixedSpace ρ A) ≤ 2 * Nat.card F := by
      by_cases hk : φ.ker = ⊥
      · have hcard' : Nat.card A ≤ 2 := by simpa only [hk, Subgroup.card_bot, mul_one] using hcard
        exact Nat.mul_le_mul hcard' (fixedSpace_card_le_of_nontrivial_coefficient ρ A a (φ a) ha (hφ a))
      · have hprod := kernel_mul_fixedSpace_card_le ρ hfaith A hA.1.2 φ hφ hk a ha
        calc
          Nat.card A * Nat.card (fixedSpace ρ A) ≤
              (2 * Nat.card φ.ker) * Nat.card (fixedSpace ρ A) := Nat.mul_le_mul_right _ hcard
          _ = 2 * (Nat.card φ.ker * Nat.card (fixedSpace ρ A)) := Nat.mul_assoc _ _ _
          _ ≤ 2 * Nat.card F := Nat.mul_le_mul_left _ hprod
    have hbad := (card_sq_le_card_mul_fixedSpace ρ hA).trans hbound
    have hlt : 2 * Nat.card F < Nat.card F * Nat.card F :=
      Nat.mul_lt_mul_of_pos_right hF (Nat.card_pos (α := F))
    exact (not_lt_of_ge hbad) hlt
  intro a ha
  exact (fieldAction_eq_one_iff ρ hsemi a).mp (htrivial ⟨a, ha⟩)

end Representation.SL2NaturalOffenders
