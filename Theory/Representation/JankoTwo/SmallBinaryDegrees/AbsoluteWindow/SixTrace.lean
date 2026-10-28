module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.FrobeniusFixedDescent
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.BinaryIrreducibility.SmallDegree

/-!
# Nonbinary traces in absolute degree six

If every trace were fixed by squaring, extension to an algebraic closure would
have the same character as its Frobenius twist. Irreducible trace equivalence
and Frobenius descent then produce a faithful six-dimensional representation
over the binary prime field. This contradicts the checked order obstruction:
25 divides the order of the literal J₂ carrier but does not divide |GL₆(2)|.

Thus the degree-six lower trace-field bound needs no modular degree catalogue
or identification with a chosen six-dimensional module.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, manuscript p.16, and the degree-six characteristic-two J₂
entry in Hiss--Malle's corrected low-degree tables.
-/

public section
open scoped TensorProduct
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
open Sporadic.LeechRelated.J2
universe v

/-- Every faithful absolutely irreducible six-dimensional module on the
actual carrier has a trace outside the binary prime field. -/
theorem degree_six_trace_separation {K U : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Carrier U) (hf : Function.Injective τ)
    (hi : τ.IsAbsolutelyIrreducible) (hd : Module.finrank K U = 6) :
    ∃ g, τ.character g ^ 2 ≠ τ.character g := by
  classical
  by_contra! htrace
  let C := AlgebraicClosure K
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Module.Finite (ZMod 2) K := Module.Finite.of_finite
  let : Algebra.IsAlgebraic (ZMod 2) C := Algebra.IsAlgebraic.trans (ZMod 2) K C
  let ρ := extendScalars C τ
  let : IsIrreducible ρ := hi.irreducible_of_closure
  let : IsIrreducible (frobeniusConjugate 2 1 ρ) := frobeniusConjugate_isIrreducible 2 1 ρ
  have hchar : ρ.character = (frobeniusConjugate 2 1 ρ).character := by
    funext g
    rw [character_frobeniusConjugate]
    change LinearMap.trace C _ ((τ g).baseChange C) =
      LinearMap.trace C _ ((τ g).baseChange C) ^ (2 ^ 1)
    rw [LinearMap.trace_baseChange, pow_one, ← map_pow]
    exact congrArg (algebraMap K C) (htrace g).symm
  have hequiv := (character_eq_iff_equiv_of_irreducible ρ
    (frobeniusConjugate 2 1 ρ)).mp hchar
  obtain ⟨σ, ⟨e⟩⟩ := exists_primeField_model_of_frobenius_equiv 2 ρ
    (Module.finBasis C (C ⊗[K] U)) hequiv
  have hfρ : Function.Injective ρ := (extendScalars_faithful_iff C τ).mp hf
  have hfσ : Function.Injective σ := by
    intro g h hgh
    apply hfρ
    have he : mapCoefficients (algebraMap (ZMod 2) C) σ g =
        mapCoefficients (algebraMap (ZMod 2) C) σ h := by
      apply LinearMap.toMatrix'.injective
      simp only [mapCoefficients_toMatrix, hgh]
    simpa only [e.conj_apply_self] using congrArg e.conj he
  apply G2FourModule.Embedding.BinaryIrreducibility.not_injective_binary_of_finrank_le_six
    σ ?_ hfσ
  simpa [Module.finrank_baseChange] using hd.le

/-- The degree-six branch is unconditional; only the degree-fourteen trace
witness is needed to finish separation in the small absolute window. -/
theorem traceSeparation_of_fourteen (hfourteen : FourteenTraceSeparation.{v}) :
    TraceSeparation.{v} := by
  intro K _ _ _ U _ _ _ τ hf hi hd
  rcases hd with hsix | hfour
  · exact degree_six_trace_separation τ hf hi hsix
  · exact hfourteen K U τ hf hi hfour

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
