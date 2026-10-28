module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The field degree and cocycle of an outer G₂ involution

Faithfulness of the actual inner-field action lets us square an automorphism
in its semidirect product: the field component has order two and the inner
component satisfies the cocycle equation. Galois fixed-point theory then
identifies the field degree as twice the degree of the actual fixed subfield.

These are the parameter and cocycle reductions for Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 16.1.4(4), printed p.1171.
They do not assert that the cocycle is a coboundary or identify the fixed group.
The displayed inner-field expression is an input; automorphism coverage is
not needed for this reduction.
-/

@[expose] public section

namespace Atlas.G2.EvenFieldFixedResidual
open LieAutomorphismExtensions
variable {F : Type*} [Field F]

/-- The actual coefficient fixed field, with its inherited inclusion into F. -/
abbrev fixedField (σ : F ≃+* F) :=
  FixedPoints.subfield (Subgroup.zpowers σ) F

/-- Squaring the faithful semilinear expression gives an involutory field
component and the actual G₂ cocycle equation. -/
theorem coefficient_involution_and_cocycle [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (a : MulAut (Model F)) (ha : a ^ 2 = 1)
    (g : Model F) (σ : F ≃+* F)
    (he : a = MulAut.conj g * fieldAction σ)
    (hout : ∀ h : Model F, a ≠ MulAut.conj h) :
    orderOf σ = 2 ∧ g * fieldAction σ g = 1 := by
  let z : Model F ⋊[fieldAction] (F ≃+* F) := ⟨g, σ⟩
  have hz : z ^ 2 = 1 := by
    apply semilinearAction_injective hq
    rw [map_pow, map_one]
    change (MulAut.conj g * fieldAction σ) ^ 2 = 1
    rw [← he]
    exact ha
  have hs : σ ^ 2 = 1 := congrArg SemidirectProduct.right hz
  have hg : g * fieldAction σ g = 1 := congrArg SemidirectProduct.left hz
  refine ⟨orderOf_eq_prime hs ?_, hg⟩
  intro hs1
  apply hout g
  simpa [hs1] using he

/-- An involutory coefficient automorphism halves the binary field degree. -/
theorem fixedField_card [Finite F] [CharP F 2]
    (σ : F ≃+* F) (hs : orderOf σ = 2) {n : ℕ} (hc : Nat.card F = 2 ^ n) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧ Nat.card (fixedField σ) = 2 ^ m := by
  let R := fixedField σ
  let : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  let : IsGaloisGroup (Subgroup.zpowers σ) R F :=
    IsGaloisGroup.fixedPoints (Subgroup.zpowers σ) F
  have hdeg : Module.finrank R F = 2 := by
    rw [← IsGaloisGroup.card_eq_finrank (Subgroup.zpowers σ) R F,
      Nat.card_zpowers, hs]
  let : Fintype R := Fintype.ofFinite R
  let : CharP R 2 := Subfield.charP R 2
  obtain ⟨m, _, hm⟩ := FiniteField.card R 2
  have hRm : Nat.card R = 2 ^ (m : ℕ) := by
    simpa [Nat.card_eq_fintype_card] using hm
  refine ⟨m, m.pos, ?_, hRm⟩
  have hcard : 2 ^ n = 2 ^ (2 * (m : ℕ)) := by
    rw [← hc, Module.natCard_eq_pow_finrank (K := R), hdeg, hRm, ← pow_mul,
      Nat.mul_comm (m : ℕ) 2]
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hcard

/-- The source cardinality hypothesis alone supplies characteristic two and
the exact field-involution parameters of the given expression. -/
theorem field_involution_parameters [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card F = 2 ^ n) (a : MulAut (Model F)) (ha : a ^ 2 = 1)
    (g : Model F) (σ : F ≃+* F)
    (he : a = MulAut.conj g * fieldAction σ)
    (hout : ∀ h : Model F, a ≠ MulAut.conj h) :
    orderOf σ = 2 ∧ g * fieldAction σ g = 1 ∧
      ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧ Nat.card (fixedField σ) = 2 ^ m := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ n by simpa [Nat.card_eq_fintype_card] using hc)
  have hq : 2 < Nat.card F := by
    rw [hc]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  obtain ⟨hs, hg⟩ := coefficient_involution_and_cocycle hq a ha g σ he hout
  exact ⟨hs, hg, fixedField_card σ hs hc⟩

end Atlas.G2.EvenFieldFixedResidual
