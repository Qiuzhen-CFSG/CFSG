module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Defs
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Two independent calculations for the degree-five actor argument

An outer involution of GL₅(2) has a nondegenerate symmetric fixed form.
Its canonical vector splits off a line, leaving an alternating four-space.
The needed comparison with S₆ must carry transpositions to actual rank-one
transvections on the original five-space. `FixedModel` specifies precisely
this comparison; it does not assert that such a comparison exists.

The independent permutation calculation concerns an injectively embedded A₆
and a subgroup of order four centralizing one of its Sylow two-subgroups.
It asks for a transposition in that same subgroup of order four.

These are intermediate contracts for the intrinsic degree-five calculation
in Aschbacher–Smith, E.6.23, printed p.254 (PDF p.265). Neither contract is
the source theorem or a substitute for its proof.
-/

@[expose] public section

namespace BinaryLinear.SixSylowActors.Five
open OuterCyclic

/-- A comparison of the actual fixed group, retaining the natural action
of the inverse images of transpositions. -/
structure FixedModel (τ : MulAut (LinearGroup 5)) where
  equiv : τ.fixedSubgroup ≃* Equiv.Perm (Fin 6)
  swap_isTransvection : ∀ σ : Equiv.Perm (Fin 6), σ.IsSwap →
    IsTransvection ((equiv.symm σ : τ.fixedSubgroup) : LinearGroup 5)

/-- The finite permutation calculation, with the supplied embedding and Sylow
subgroup retained. Its proof is independent of the outer-involution geometry. -/
def PermutationSylowSwap : Prop :=
  ∀ (ι : alternatingGroup (Fin 6) →* Equiv.Perm (Fin 6)), Function.Injective ι →
    ∀ (Q : Sylow 2 (alternatingGroup (Fin 6))) (B : Subgroup (Equiv.Perm (Fin 6))),
      Nat.card B = 4 →
      (∀ b ∈ B, ∀ x ∈ (Q : Subgroup (alternatingGroup (Fin 6))),
        Commute b (ι x)) →
      ∃ b ∈ B, b.IsSwap

end BinaryLinear.SixSylowActors.Five
