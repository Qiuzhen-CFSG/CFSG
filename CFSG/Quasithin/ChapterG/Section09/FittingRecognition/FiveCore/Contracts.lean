module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The two independent linear calculations in the five-core branch

The first contract asks for pointwise fixed vectors in the actual ordinary
factor spaces of the G.9.2 decomposition. The second is a normalizer lemma
inside the actual linear group: a subgroup containing a normal five-cycle
has dihedral normal closure for each nontrivial elementary two-subgroup.
Its producer works in dimension four. Neither contract is a field of the
source Fitting hypothesis, and the branch assembly must discharge both.

Source: Aschbacher--Smith, G.9.4, printed pp.354--355, PDF pp.365--366.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore

open NilpotentRigidity

universe u v

variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- Fixing the ordinary factors is an assertion about their literal moved
spaces, including the natural OmegaFour action. -/
def OrdinaryFactorsFixed (ρ : Representation (ZMod 2) G V) (A : Subgroup G) : Prop :=
  ∀ H : Subgroup G, H ≤ fittingSubgroup G ⊔ A →
    ∀ d : ClassifiedDecomposition ρ H True, ∀ i : Fin d.count, 0 < i.val →
      movedSpace ρ (d.internal.factor i) ≤
        Representation.invariants (ρ.comp (pCore 5 G).subtype)

/-- The GL₄(2) five-normalizer calculation with its overgroup application.
The closure is taken in the specified linear subgroup L, not in all of GL(V). -/
def LinearNormalizerRecognition (V : Type v) [AddCommGroup V] [Module (ZMod 2) V] : Prop :=
  ∀ (L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) (X E : Subgroup L),
    X.Normal → Nat.card X = 5 → IsElementaryAbelian 2 E → E ≠ ⊥ →
      Nonempty (Subgroup.normalClosure (E : Set L) ≃* DihedralGroup 5)

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore
