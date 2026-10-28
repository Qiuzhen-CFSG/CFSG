module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts

/-!
# Concrete model inputs for Hall--Janko modular saturation

The proposed nontrivial characteristic-two candidates have degrees
6, 6, 14, 14, 36, 64, 64, 84 and 160. The two families below request actual
simple actions of the literal degree-100 carrier, with pairwise inequivalence
over each algebraically closed coefficient field. They do not assert that
such actions exist, or that these degrees exhaust the simple modules.

The assembly adds the trivial action, proves cross-family inequivalence by
dimension, and applies the independent odd-order class bound. Model producers
must verify carrier descent and irreducibility after scalar extension.

Sources: ATLAS of Finite Group Representations, J2 characteristic-two matrix
candidates (`J2G1-f4r6aB0`, `f4r14aB0`, `f2r36B0`, `f4r64aB0`, `f2r84B0`,
`f2r160B0`); Hiss--Malle corrected Table 2 specifies the low-degree target.
The tables are candidate data, not completeness or irreducibility proofs.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
open Sporadic.LeechRelated.J2
universe v

/-- Proposed dimensions of the four nontrivial candidates in the small window. -/
@[expose] def smallDegree : Fin 4 → ℕ := ![6, 6, 14, 14]

/-- Proposed dimensions of the five candidates above the small window. -/
@[expose] def largeDegree : Fin 5 → ℕ := ![36, 64, 64, 84, 160]

/-- An actual simple family with its precise coordinate spaces and inequivalence.
Existence is deliberately separate from this specification. -/
@[expose] def ModelsExist {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
    ∃ (ρ : ∀ i, Representation F Carrier (Fin (d i) → F)),
      (∀ i, IsIrreducible (ρ i)) ∧
      Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))

/-- Independent construction obligation for degrees 6, 6, 14 and 14. -/
@[expose] def SmallModelsExist : Prop := ModelsExist.{v} smallDegree

/-- Independent construction obligation for degrees 36, 64, 64, 84 and 160. -/
@[expose] def LargeModelsExist : Prop := ModelsExist.{v} largeDegree

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
