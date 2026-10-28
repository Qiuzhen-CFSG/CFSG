module
public import CFSG.Quasithin.ChapterD.Section03.EvenKernelConstituents
public import Theory.Representation.SL2.PairHermitian
public import Theory.Representation.BinaryOffender.PairActorRank

/-!
# Actual multiplicity actions for Hermitian square constituents

A genuine Hermitian constituent constructs a faithful action of the opposite
SL₂ factor over the fixed half-field. This action needs at least four
coordinates, so the unchanged binary square has dimension at least 8n.
Both original nonzero actor kernels and both original constituents are kept.
Conjugation on both factors bounds the full preserving actor by 2n. A member
moving the Schur field therefore forces equality in all dimension budgets;
at equality the multiplicity action has exactly four coordinates.
The original Chapter 10 Hall consumer applies this without adding premises.
This is a dimension obstruction, not an exclusion of the Hermitian square.
Source: Aschbacher--Smith D.3.7, printed pp.198--199, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {n : ℕ}

/-- An actor moving the Schur field can meet the Hermitian dimension bound
only at equality in the full-actor rank and fixed-codimension budgets. -/
theorem even_square_schur_nonlinear_saturation
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ) (hn : 2 ≤ n)
    (hd : 8*n ≤ Module.finrank (ZMod 2) V)
    (A : Subgroup (SquarePreserving.group σ))
    (hA : A ∈ QhatStar (SquarePreserving.action σ))
    (a : SquarePreserving.group σ) (ha : a ∈ A)
    (hlin : ¬ SchurNormalizer.IsSchurLinear σ (SquarePreserving.toNormalizer σ a)) :
    Module.finrank (ZMod 2) V = 8*n ∧ rank A = 2*n ∧
      fixedCodim (SquarePreserving.action σ) A = 4*n := by
  let := hi
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hr := SquarePreserving.even_elementary_rank_le σ hi hf n hn
    (GaloisField.card 2 n (by omega)) A
  have hb := (actionRatio_le_nat_iff (SquarePreserving.action σ) hA.1.2.1 2).mp
    (hA.1.2.2.2.le.trans hA.1.1)
  have he := SchurNormalizer.finrank_le_twice_fixedCodim σ
    (SquarePreserving.toNormalizer σ a) hlin
  rw [fixedCodim_zpowers_eq_displacement_rank] at he
  have hm := NaturalTensor.operatorFixedCodim_le_fixedCodim
    (SquarePreserving.action σ) A ha
  change Module.finrank (ZMod 2) (a.val.val-1).range ≤ _ at hm
  change Module.finrank (ZMod 2) V ≤ 2*Module.finrank (ZMod 2) (a.val.val-1).range at he
  omega

/-- The same original preserving actor, with both kernels and a sharp
constraint on every element that moves the Schur field. -/
@[expose] def EvenSquareHermitianActor
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V) : Prop :=
  ∃ A : Subgroup (SquarePreserving.group σ),
    A ∈ QhatStar (SquarePreserving.action σ) ∧
    A ⊓ centralizer (SquarePreserving.left σ : Set _) ≠ ⊥ ∧
    A ⊓ centralizer (SquarePreserving.right σ : Set _) ≠ ⊥ ∧
    Disjoint (A ⊓ centralizer (SquarePreserving.left σ : Set _))
      (A ⊓ centralizer (SquarePreserving.right σ : Set _)) ∧
    rank A ≤ 2*n ∧ fixedCodim (SquarePreserving.action σ) A ≤ 4*n ∧
    ∀ a ∈ A, ¬ SchurNormalizer.IsSchurLinear σ (SquarePreserving.toNormalizer σ a) →
      Module.finrank (ZMod 2) V = 8*n ∧ rank A = 2*n ∧
        fixedCodim (SquarePreserving.action σ) A = 4*n

/-- The original Hermitian alternative with constructed multiplicity actions
and the resulting lower bound, retaining both component-action kernels. -/
@[expose] def EvenSquareHermitianMultiplicity
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V) : Prop :=
  EvenSquareHermitianKernel σ n ∧
    8*n ≤ Module.finrank (ZMod 2) V ∧
    (∃ s : ℕ, n = 2*s ∧ ∃ hs : 1 < s, letI : NeZero s := ⟨(by omega)⟩;
      SL2.PairHermitian.Coordinates s σ ∨
        SL2.PairHermitian.Coordinates s (σ.comp MulEquiv.prodComm.toMonoidHom)) ∧
    EvenSquareHermitianActor σ

/-- The entire opposite component acts faithfully on the actual multiplicity
space; the original actor is not replaced by a faithful one-factor image. -/
theorem even_square_hermitian_multiplicity
    [IsSimpleGroup SL(2,GaloisField 2 n)] [IsQuasisimple SL(2,GaloisField 2 n)]
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (hk : EvenSquareHermitianKernel σ n) : EvenSquareHermitianMultiplicity σ := by
  let := hi
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have hk' := hk
  obtain ⟨_,_,_,s,hs,hpos,hherm⟩ := hk'
  let : NeZero s := ⟨by omega⟩
  have hF : Nat.card (GaloisField 2 n) = 2^(2*s) := by
    rw [GaloisField.card 2 n (by omega),hs]
  have hactor (hd : 8*n ≤ Module.finrank (ZMod 2) V) : EvenSquareHermitianActor σ := by
    obtain ⟨A,hA,hL,hK,hdis⟩ := hk.1
    let : IsElementaryAbelian 2 A := hA.1.2.1.2
    have hr := SquarePreserving.even_elementary_rank_le σ hi hf n (by omega)
      (GaloisField.card 2 n (by omega)) A
    have hb := (actionRatio_le_nat_iff (SquarePreserving.action σ) hA.1.2.1 2).mp
      (hA.1.2.2.2.le.trans hA.1.1)
    exact ⟨A,hA,hL,hK,hdis,hr,(by omega),fun a ha hlin =>
      even_square_schur_nonlinear_saturation σ hi hf (by omega) hd A hA a ha hlin⟩
  rcases hherm with ⟨I,hI,_,_,_,hmodel⟩ | ⟨I,hI,_,_,_,hmodel⟩
  · have hc := SL2.PairHermitian.coordinates_of_constituent s σ hf I hI hmodel
    have hd := SL2.PairHermitian.degree_lower_bound s hF σ hc
    exact ⟨hk,(by omega),⟨s,hs,hpos,Or.inl hc⟩,hactor (by omega)⟩
  · let swap : (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) ≃*
        (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) := MulEquiv.prodComm
    let τ : Representation (ZMod 2)
        (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V := σ.comp swap.toMonoidHom
    let : τ.IsIrreducible :=
      (irreducible_comp_surjective_iff swap.toMonoidHom swap.surjective σ).mpr hi
    have hfτ : Function.Injective τ := hf.comp swap.injective
    have hc := SL2.PairHermitian.coordinates_of_constituent s τ hfτ I hI hmodel
    have hd := SL2.PairHermitian.degree_lower_bound s hF τ hc
    exact ⟨hk,(by omega),⟨s,hs,hpos,Or.inr hc⟩,hactor (by omega)⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- At equality the Hermitian multiplicity action is genuinely a faithful
four-dimensional action over the half-field, in one of the original orientations. -/
theorem even_square_hermitian_four_action_of_degree_eq
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V)
    (hm : EvenSquareHermitianMultiplicity σ) (hd : Module.finrank (ZMod 2) V = 8*n) :
    ∃ s : ℕ, n = 2*s ∧ ∃ hs : 1 < s, letI : NeZero s := ⟨(by omega)⟩;
      ∃ μ : Representation (OrthogonalFourMinus.FiniteModel.fixedField s)
        SL(2,GaloisField 2 n) (Fin 4 → OrthogonalFourMinus.FiniteModel.fixedField s),
        Function.Injective μ := by
  obtain ⟨s,hs,hpos,hc⟩ := hm.2.2.1
  let : NeZero s := ⟨by omega⟩
  refine ⟨s,hs,hpos,?_⟩
  rcases hc with hc | hc
  · obtain ⟨_,_,μ,hμ,_,_⟩ := SL2.PairHermitian.four_coordinates_of_degree_eq s σ hc (by omega)
    exact ⟨μ,hμ⟩
  · obtain ⟨_,_,μ,hμ,_,_⟩ := SL2.PairHermitian.four_coordinates_of_degree_eq s
      (σ.comp MulEquiv.prodComm.toMonoidHom) hc (by omega)
    exact ⟨μ,hμ⟩
end CFSG.Quasithin.ChapterD
