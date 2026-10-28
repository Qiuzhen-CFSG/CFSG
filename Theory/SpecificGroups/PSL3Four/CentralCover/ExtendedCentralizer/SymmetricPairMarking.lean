module


public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.Geometry
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Perm

/-!
# Marked involutions in the symmetric-group product

A commuting graph and field pair, with the field involution inverting
the cubic subgroup, determines the two symmetric factors up to conjugacy
and interchange. A finite certificate on the36-element product proves
that assertion, and the equivalence transport retains the actual actors.

Source: Aschbacher–Smith15.3.38, printed pp.1136–1137.
-/

public section
open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.SymmetricPairMarking
abbrev Pair := SymmetricThree × SymmetricThree
local instance : Fintype SymmetricThree := fintypePerm

set_option synthInstance.maxSize 256 in
set_option maxRecDepth 10000 in
private theorem alignment_certificate : ∀ a b : Pair,
    a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → a ≠ b → a * b = b * a →
    (∀ x : Pair, x ^ 3 = 1 → b * x * b⁻¹ = x⁻¹) →
    ∃ g : Pair,
      ((g * a * g⁻¹ = (1, reflection) ∧
        g * b * g⁻¹ = (reflection, reflection)) ∨
       (g * a * g⁻¹ = (reflection, 1) ∧
        g * b * g⁻¹ = (reflection, reflection))) := by
  decide +kernel

/-- The graph and field pair determines marked coordinates, up to interchanging
the two factors and conjugating inside them. -/
theorem aligned_equiv {H : Type*} [Group H] (e : H ≃* Pair) (a b : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hab : a ≠ b)
    (hc : a * b = b * a)
    (hinv : ∀ x : H, x ^ 3 = 1 → b * x * b⁻¹ = x⁻¹) :
    ∃ q : H ≃* Pair, q a = (1, reflection) ∧ q b = (reflection, reflection) := by
  have hpow (x : H) (hx : x ^ 2 = 1) : e x ^ 2 = 1 := by
    rw [← map_pow, hx, map_one]
  have hi : ∀ x : Pair, x ^ 3 = 1 → e b * x * (e b)⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : y ^ 3 = 1 := e.injective (by rw [map_pow, hx, map_one])
    simpa only [map_mul, map_inv] using congrArg e (hinv y hy)
  obtain ⟨g, h | h⟩ := alignment_certificate (e a) (e b) (hpow a ha) (hpow b hb)
    (fun hh => ha1 (e.injective (hh.trans (map_one e).symm)))
    (fun hh => hab (e.injective hh)) (by simpa only [map_mul] using congrArg e hc) hi
  · exact ⟨e.trans (MulAut.conj g), h⟩
  · refine ⟨(e.trans (MulAut.conj g)).trans MulEquiv.prodComm, ?_, ?_⟩
    · change (g * e a * g⁻¹).swap = (1, reflection)
      rw [h.1]
      rfl
    · change (g * e b * g⁻¹).swap = (reflection, reflection)
      rw [h.2]
      rfl

end Matrix.PSL3Four.ExtendedCentralizer.SymmetricPairMarking
