module
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.CentralKernel
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness

/-!
# Cardinal duality for the triality root pairings

The cubic trace pairing is bilinear over the genuine Frobenius fixed field.
For a subspace W, nondegeneracy gives |W| |Wᗮ| = |V|. A pairwise
orthogonal set therefore has an isotropic span of order at most √|V|;
no scalar closure of the original set is needed. The two hyperbolic forms
below are used by the arms radical and the zero-first-coordinate central
radical. The trace annihilator is used by the remaining central branch.

Source: the trace root relations in GLS3 2.4.5(b)(4) and §2.6
(`refs/KGroup/GLS3/chapter2.tex`), for the rank calculation on printed
p.356 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Triality.Standard.RadicalCoordinates.Centers
namespace Triality.Standard.TwoRank.RadicalBounds

theorem pairing_smul_right (P : Parameters) (t : fixedField P)
    (a b : ExtensionField P) : armsPairing P a (t • b) = t * armsPairing P a b := by
  apply Subtype.ext
  have ht : fieldFrobenius P t.val = t.val := t.property
  change (armsPairing P a (t.val * b)).val = _
  simp only [armsPairing_coe, Subfield.coe_mul, map_mul, ht]
  ring

/-- The root trace pairing is bilinear over the actual Frobenius fixed field. -/
def traceForm (P : Parameters) : LinearMap.BilinForm (fixedField P) (ExtensionField P) where
  toFun a := {
    toFun := armsPairing P a
    map_add' := armsPairing_add_right P a
    map_smul' t b := pairing_smul_right P t a b }
  map_add' a b := by apply LinearMap.ext; intro c; exact armsPairing_add_left P a b c
  map_smul' t a := by apply LinearMap.ext; intro b; exact armsPairing_fixed_mul_left P t a b

@[simp] theorem traceForm_apply (P : Parameters) (a b : ExtensionField P) :
    traceForm P a b = armsPairing P a b := rfl

theorem traceForm_nondegenerate (P : Parameters) (hp : P.prime = 2) :
    (traceForm P).Nondegenerate :=
  ⟨armsPairing_left_nondegenerate P hp, armsPairing_right_nondegenerate P hp⟩

/-- Cardinal duality for a subspace and its right annihilator. -/
theorem card_mul_card_orthogonal {k V : Type*} [Field k] [Finite k]
    [AddCommGroup V] [Module k V] [Finite V]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate) (W : Submodule k V) :
    Nat.card W * Nat.card (B.orthogonal W) = Nat.card V := by
  have h := B.finrank_add_finrank_orthogonal' W
  rw [hB.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero] at h
  rw [Module.natCard_eq_pow_finrank (K := k) (V := W),
    Module.natCard_eq_pow_finrank (K := k) (V := B.orthogonal W), ← pow_add, h,
    ← Module.natCard_eq_pow_finrank (K := k) (V := V)]

/-- Bilinearity, rather than scalar closure of the set, makes its span isotropic. -/
theorem span_le_orthogonal_span {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (B : LinearMap.BilinForm k V)
    (s : Set V) (hs : ∀ x ∈ s, ∀ y ∈ s, B x y = 0) :
    Submodule.span k s ≤ B.orthogonal (Submodule.span k s) := by
  apply Submodule.span_le.mpr
  intro y hy x hx
  exact Submodule.span_induction
    (fun x hx => hs x hx y hy)
    (by simp)
    (fun x z _ _ hx hz => by simp [map_add, hx, hz])
    (fun a x _ hx => by simp [map_smul, hx]) hx

theorem card_span_sq_le {k V : Type*} [Field k] [Finite k]
    [AddCommGroup V] [Module k V] [Finite V]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (s : Set V) (hs : ∀ x ∈ s, ∀ y ∈ s, B x y = 0) :
    Nat.card (Submodule.span k s) ^ 2 ≤ Nat.card V := by
  rw [← card_mul_card_orthogonal B hB (Submodule.span k s), pow_two]
  exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective _
    (Submodule.inclusion_injective (span_le_orthogonal_span B s hs)))

end Triality.Standard.TwoRank.RadicalBounds

namespace Triality.Standard.TwoRank.RadicalBounds

/-- A hyperbolic form made from any perfect pairing. -/
def hyperbolic {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : LinearMap.BilinForm k (V × V) where
  toFun x := {
    toFun y := B x.1 y.2 + B y.1 x.2
    map_add' y z := by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; abel
    map_smul' t y := by simp [map_smul, mul_add] }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change B (x.1 + z.1) y.2 + B y.1 (x.2 + z.2) =
      (B x.1 y.2 + B y.1 x.2) + (B z.1 y.2 + B y.1 z.2)
    simp only [map_add, LinearMap.add_apply]
    abel
  map_smul' t x := by apply LinearMap.ext; intro y; simp [map_smul, mul_add]

@[simp] theorem hyperbolic_apply {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (x y : V × V) :
    hyperbolic B x y = B x.1 y.2 + B y.1 x.2 := rfl

theorem hyperbolic_nondegenerate {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate) :
    (hyperbolic B).Nondegenerate := by
  have hl (x : V × V) (h : ∀ y, hyperbolic B x y = 0) : x = 0 := by
    apply Prod.ext
    · exact hB.1 x.1 (fun y => by simpa using h (0, y))
    · exact hB.2 x.2 (fun y => by simpa using h (y, 0))
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  simpa only [hyperbolic_apply, add_comm] using hx y

/-- Add the fixed-field root pair to the cubic root pairing. -/
def extendedTrace (P : Parameters) :
    LinearMap.BilinForm (fixedField P) (ExtensionField P × fixedField P) where
  toFun x := {
    toFun y := traceForm P x.1 y.1 + x.2 * y.2
    map_add' y z := by simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add]; abel
    map_smul' t y := by simp [map_smul, mul_add]; ring }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change traceForm P (x.1 + z.1) y.1 + (x.2 + z.2) * y.2 =
      (traceForm P x.1 y.1 + x.2 * y.2) + (traceForm P z.1 y.1 + z.2 * y.2)
    simp only [map_add, LinearMap.add_apply, add_mul]
    abel
  map_smul' t x := by apply LinearMap.ext; intro y; simp [map_smul, mul_add, mul_assoc]

@[simp] theorem extendedTrace_apply (P : Parameters)
    (x y : ExtensionField P × fixedField P) :
    extendedTrace P x y = armsPairing P x.1 y.1 + x.2 * y.2 := rfl

theorem extendedTrace_nondegenerate (P : Parameters) (hp : P.prime = 2) :
    (extendedTrace P).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · exact armsPairing_left_nondegenerate P hp x.1 (fun y => by simpa using hx (y, 0))
    · simpa using hx (0, 1)
  · intro y hy
    apply Prod.ext
    · exact armsPairing_right_nondegenerate P hp y.1 (fun x => by simpa using hy (x, 0))
    · simpa using hy (0, 1)

end Triality.Standard.TwoRank.RadicalBounds
