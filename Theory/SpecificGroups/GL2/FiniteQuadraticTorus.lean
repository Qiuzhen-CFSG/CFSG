module
public import Theory.SpecificGroups.GL2.QuadraticRegularRepresentation
public import Mathlib.FieldTheory.Finite.Extension

/-!
# The quadratic finite-field torus and its Frobenius reflection

For a finite field F of characteristic prime p, the units of the actual
quadratic extension embed in GL2(F). An external involution conjugates
multiplication by a unit to multiplication by its q-th power, where q=|F|.
Base-field units go to the actual scalar matrices.

The canonical Frobenius of FiniteField.Extension F p 2 has order two.
Specializing the quadratic regular representation gives the embedding and
reflection; its established pointwise Frobenius equation identifies the
conjugation exponent. The exact extension algebra and automorphism
instances are retained.

This is the concrete quadratic-torus input for the linear semidihedral
Sylow model in Alperin--Brauer--Gorenstein II.2 Lemma 1 and II.3 Proposition 3
(article pages 17 and 26). The representation itself needs no parity
restriction on the base field.
-/

namespace Matrix.GeneralLinearGroup

public theorem exists_finite_quadratic_torus
    (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    let E := FiniteField.Extension F p 2
    ∃ (ρ : Eˣ →* GL (Fin 2) F) (w : GL (Fin 2) F),
      Function.Injective ρ ∧ w ^ 2 = 1 ∧ w ∉ ρ.range ∧
      (∀ a : Eˣ, w * ρ a * w⁻¹ = ρ (a ^ Nat.card F)) ∧
      ∀ c : Fˣ, ρ (Units.map (algebraMap F E).toMonoidHom c) = scalar (Fin 2) c := by
  let : Fintype F := Fintype.ofFinite F
  let E := FiniteField.Extension F p 2
  let σ := FiniteField.Extension.frob F p 2
  have ho : orderOf σ = 2 := by
    change orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic F E) = 2
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      FiniteField.finrank_extension]
  have hs : σ ^ 2 = 1 := by simpa only [ho] using pow_orderOf_eq_one σ
  have hn : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ho
    omega
  obtain ⟨ρ, w, hi, hw, he, ha, hc⟩ := exists_quadratic_regular_representation F E
    (FiniteField.finrank_extension F p 2) σ hs hn
  refine ⟨ρ, w, hi, hw, he, ?_, hc⟩
  intro a
  rw [ha]
  apply congrArg ρ
  apply Units.ext
  exact FiniteField.Extension.frob_apply F p 2

end Matrix.GeneralLinearGroup
