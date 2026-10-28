module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.BinaryModels
public import Theory.Representation.ScalarDescent
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Scalar extension of the larger binary M₂₄ models

Extend each binary module to the given coefficient field, then use the
extended standard basis to obtain the exact coordinate carrier required by
`LargeModelsExist`. Absolute irreducibility supplies irreducibility. An
equivalence between two extended coordinate representations would descend
to a binary intertwining equivalence, so inequivalence is also preserved.

The resulting theorem is conditional on actual binary construction
certificates. It supplies the field-uniform part of the larger-model input
to `absoluteSmallSpectrum_of_models`, not the missing finite constructions.

Source: the M₂₄ degree window in Guralnick–Malle, *Classification of
2F-modules I*, Proposition 5.1, manuscript p.17; James, J. Algebra 27
(1973), 57–111. The scalar-extension argument uses the general results in
`AbsolutelyIrreducible` and `ScalarDescent`.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
open Sporadic.Mathieu
universe v

/-- Coordinates in the scalar extension of the binary standard basis. -/
def extensionCoordinates (F : Type v) [Field F] [Algebra (ZMod 2) F] (n : ℕ) :
    (F ⊗[ZMod 2] (Fin n → ZMod 2)) ≃ₗ[F] (Fin n → F) :=
  ((Pi.basisFun (ZMod 2) (Fin n)).baseChange F).equivFun

/-- The actual extended representation on the required coordinate carrier. -/
def coordinateExtension (F : Type v) [Field F] [Algebra (ZMod 2) F]
    {n : ℕ} (ρ : Representation (ZMod 2) M24 (Fin n → ZMod 2)) :
    Representation F M24 (Fin n → F) :=
  (extensionCoordinates F n).conjRingEquiv.toMonoidHom.comp (extendScalars F ρ)

/-- The coordinate change intertwines the genuine tensor-product action. -/
def extensionEquiv (F : Type v) [Field F] [Algebra (ZMod 2) F]
    {n : ℕ} (ρ : Representation (ZMod 2) M24 (Fin n → ZMod 2)) :
    (extendScalars F ρ) ≃ₗ coordinateExtension F ρ :=
  .mk (extensionCoordinates F n) (by
    intro g
    ext x
    simp [coordinateExtension, LinearEquiv.conjRingEquiv])

/-- Absolute binary irreducibility gives irreducibility after the coordinate
change over any extension field. -/
theorem coordinateExtension_irreducible (F : Type v) [Field F] [Algebra (ZMod 2) F]
    {n : ℕ} (ρ : Representation (ZMod 2) M24 (Fin n → ZMod 2))
    [ρ.IsAbsolutelyIrreducible] : (coordinateExtension F ρ).IsIrreducible := by
  exact (RepEquiv.irreducible_euqiv (extensionEquiv F ρ)).mp
    (IsAbsolutelyIrreducible.irreducible_of_extension ρ F)

/-- Inequivalence of finite-dimensional binary representations survives
arbitrary extension of the coefficient field and the coordinate changes. -/
theorem coordinateExtension_inequivalent (F : Type v) [Field F] [Algebra (ZMod 2) F]
    {n m : ℕ}
    (ρ : Representation (ZMod 2) M24 (Fin n → ZMod 2))
    (σ : Representation (ZMod 2) M24 (Fin m → ZMod 2))
    (h : IsEmpty (ρ.Equiv σ)) :
    IsEmpty ((coordinateExtension F ρ).Equiv (coordinateExtension F σ)) := by
  constructor
  intro e
  obtain ⟨e'⟩ := repEquiv_of_extendScalars ρ σ
    ⟨(extensionEquiv F ρ).trans
      ((RepEquiv.ofRepresentationEquiv e).trans (extensionEquiv F σ).symm)⟩
  exact h.false e'.toRepresentationEquiv

/-- Eight actual binary models suffice for the exact field-uniform contract.
The construction and the binary inequivalence certificates remain explicit. -/
theorem largeModelsExist_of_binaryFamily
    (d : Fin 8 → ℕ) (ρ : ∀ i, Representation (ZMod 2) M24 (Fin (d i) → ZMod 2))
    (habs : ∀ i, (ρ i).IsAbsolutelyIrreducible)
    (hne : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
    (hd : ∀ i, 48 < d i) : LargeModelsExist.{v} := by
  intro F _ _ _
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  refine ⟨d, fun i => coordinateExtension F (ρ i), ?_, ?_, hd⟩
  · intro i
    let := habs i
    exact coordinateExtension_irreducible F (ρ i)
  · intro i j hij
    exact coordinateExtension_inequivalent F (ρ i) (ρ j) (hne hij)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
