module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Intrinsic model contracts for the A₄ extraction

Two independent intrinsic facts remain to be supplied to the source application.
A quasisimple cover of A₆ with two-group center has only central involutions
unless its center is trivial. In S₆, a two-perfect subgroup of A₆ whose order
is divisible by six and which centralizes an involution is A₄. The second
statement concerns the actual embedding, not just the isomorphism type of an
ambient group. These are universal contracts, not assertions of either fact.

The source application constructs the noncentral involution from the marked
binary A₅ module and uses the literal normalizer quotient for the embedding.
Source: Aschbacher–Smith, proof of 13.6.6, printed p.927; GLS3, §5.2 for
central covers and involution centralizers of alternating groups.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
open Subgroup Theory.GroupTheory
universe u

/-- The intrinsic central-cover fact needed to lift the A₆ quotient. -/
def SixCoverRigidity : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q] [IsQuasisimple Q],
    pPrimeCore 2 Q = ⊥ → (Q ⧸ center Q) ≃* alternatingGroup (Fin 6) →
    (∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) → center Q = ⊥

/-- The intrinsic local recognition fact, with its literal S₆ embedding. -/
def SixLocalRecognition : Prop :=
  ∀ D : Subgroup (Equiv.Perm (Fin 6)), D ≤ alternatingGroup (Fin 6) →
    IsPPerfect 2 D → 3 ∣ Nat.card D → 2 ∣ Nat.card D →
    ∀ σ : Equiv.Perm (Fin 6), orderOf σ = 2 → σ ∈ centralizer (D : Set _) →
      Nonempty (D ≃* alternatingGroup (Fin 4))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
