module
public import CFSG.Quasithin.ChapterD.Section03.EvenHermitianMultiplicity
public import Theory.Representation.BinaryOffender.SchurNormalizerSaturation

/-!
# Schur linearity of every remaining Hermitian actor

The Hermitian multiplicity lower bound is 8n, while the full preserving actor
has rank at most 2n and displacement at most 4n. A Schur-moving member forces
equality. The strict semilinear bound then makes the entire actor rank at most
one, contradicting its saturated rank 2n. Thus every preserving starred actor
is linear over the original seed's Schur field. Both component kernels and the
actual multiplicity action remain in the output.

The literal Chapter 10 Hall application is in SeedAnalysis/EvenHermitianSchur.
This excludes Schur movement, not the remaining Schur-linear Hermitian seeds.
Source: Aschbacher--Smith D.3.7, printed pp.198--199, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {n : ℕ}

/-- Every small preserving actor on a Hermitian-sized square is Schur linear. -/
theorem even_square_hermitian_actor_schur_linear
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ) (hn : 2 ≤ n)
    (hd : 8*n ≤ Module.finrank (ZMod 2) V)
    (A : Subgroup (SquarePreserving.group σ))
    (hA : A ∈ QhatStar (SquarePreserving.action σ)) :
    ∀ a ∈ A, SchurNormalizer.IsSchurLinear σ (SquarePreserving.toNormalizer σ a) := by
  let := hi
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  intro a ha
  by_contra hlin
  obtain ⟨hdim,hr,hc⟩ := even_square_schur_nonlinear_saturation σ hi hf hn hd A hA a ha hlin
  let f := SquarePreserving.toNormalizer σ
  let B := A.map f
  have hfi : Function.Injective f := inclusion_injective _
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hrB : rank B = rank A := rank_map_injective f hfi A
  have hcB : fixedCodim (normalizerRepresentation σ) B = fixedCodim (SquarePreserving.action σ) A := by
    exact (fixedCodim_map_equivariant (SquarePreserving.action σ) (normalizerRepresentation σ)
      f (LinearEquiv.refl _ _) (fun _ _ => rfl) A).symm
  have hh := SchurNormalizer.finrank_lt_twice_fixedCodim σ B (by omega)
    (f a) (mem_map_of_mem f ha) hlin
  rw [hcB,hc,hdim] at hh
  omega

/-- The full multiplicity and kernel data, now with no Schur-moving preserving actor. -/
@[expose] def EvenSquareHermitianLinearMultiplicity
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V) : Prop :=
  EvenSquareHermitianMultiplicity σ ∧
    ∀ A : Subgroup (SquarePreserving.group σ), A ∈ QhatStar (SquarePreserving.action σ) →
      ∀ a ∈ A, SchurNormalizer.IsSchurLinear σ (SquarePreserving.toNormalizer σ a)

/-- The strengthened Hermitian alternative retains every original actor kernel. -/
theorem even_square_hermitian_linear_multiplicity
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (hm : EvenSquareHermitianMultiplicity σ) : EvenSquareHermitianLinearMultiplicity σ := by
  obtain ⟨s,hs,hpos,_⟩ := hm.2.2.1
  exact ⟨hm,fun A hA => even_square_hermitian_actor_schur_linear σ hi hf (by omega) hm.2.1 A hA⟩
end CFSG.Quasithin.ChapterD
