module

public import Theory.Representation.BinaryOffender.CentralizerField
public import Theory.GroupTheory.PResidual.Defs
public import Theory.PGroupCore

/-!
# A.1.41: the centralizer of an Irr⁺ section

Let I be an actual Irr⁺ X-submodule in a finite-dimensional binary
representation, with X = O²(X) and O₂(Aut_X(I)) = 1. The action on I is
`invariantSubspace.toRepresentation`, and Aut_X(I) is its actual image in
GL(I). The induced action on the literal quotient I/C_I(X) embeds its
linear centralizer in the quotient's linear centralizer. The latter is
the unit group of the actual X-endomorphism field of that quotient, so
the original centralizer is cyclic of odd order.

The proof strengthens the source's kernel argument: an equivariant map
into C_I(X) kills [I,X] = I. Schur and Wedderburn then give the finite
field and its unit group. The residual and two-core hypotheses are
retained in the source theorem, though the stronger kernel argument does
not need them.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, A.1.41, printed p.31 (PDF p.42).
-/

public section

open Representation Representation.BinaryOffender Representation.CentralizerField
open Representation.BinaryOffender.CentralizerField

namespace CFSG.Quasithin.ChapterA

/-- A.1.41, with the source residual and actual action-image two-core hypotheses.
The two equivalences describe the subgroup embedding and the quotient centralizer;
the field assertion concerns the literal quotient's intertwining endomorphism ring. -/
theorem lemma_A_1_41
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G)
    (_hX : pResidual 2 X = ⊤) (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ X I)
    (_hcore : pCore 2 (actionImage (invariantSubspace ρ X I hI.choose).toRepresentation) = ⊥) :
    let σ := (invariantSubspace ρ X I hI.choose).toRepresentation
    let τ := centralQuotientRepresentation ρ X I hI.choose
    Function.Injective (centralizerToQuotientUnits ρ X I hI.choose) ∧
    Nonempty (linearCentralizer σ ≃*
      (centralizerQuotientHom ρ X I hI.choose).range) ∧
    Nonempty (linearCentralizer τ ≃* (IntertwiningMap τ τ)ˣ) ∧
    IsField (IntertwiningMap τ τ) ∧ Finite (IntertwiningMap τ τ) ∧
    CharP (IntertwiningMap τ τ) 2 ∧
    IsCyclic (linearCentralizer σ) ∧ Odd (Nat.card (linearCentralizer σ)) := by
  let := hI.choose_spec.2
  refine ⟨centralizerToQuotientUnits_injective ρ X I hI.choose hI.choose_spec.1,
    ⟨centralizerQuotientRangeEquiv ρ X I hI.choose hI.choose_spec.1⟩,
    ⟨centralizerUnitsEquiv _⟩, end_isField _, end_finite _, end_charP _ 2, ?_⟩
  exact centralizer_cyclic_odd ρ X I hI.choose hI.choose_spec.1 hI.choose_spec.2

end CFSG.Quasithin.ChapterA
