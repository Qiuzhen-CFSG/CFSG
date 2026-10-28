module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.ChevalleySource.Commutators
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.ChevalleySource.Torus

/-!
# The native Spin D4 Chevalley system

All clauses of the source Chevalley system hold for the original Clifford
root points, normalizer words and coroot words. The construction combines
actual root exchange, Weyl conjugation and torus-coordinate proofs, with no
Chevalley existence or representation-classification premise.
Source: GLS3, Theorem 1.12.1.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.SimplyConnected.Pinning.ChevalleySource
noncomputable section
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

theorem isChevalleySystem : IsChevalleySystem (pinnedRootData k) (data k)
    (typeDRootPairing 2) Equiv.ulift (typeDRootPairing_base 2) := by
  refine ⟨parametrizes k, normalizer_word k, coroot_word k, root_addition k,
    commutator_formula k, coroots_commute k, coroot_multiplication k,
    ⟨fun r => Torus.coefficients r.down, ?_, ?_⟩, ?_, ?_, ?_, torus_conjugation k,
    ⟨fun _ _ => 1, fun _ _ => Or.inl rfl, ?_, reflection_coroot k, ?_⟩,
    normalizer_square k⟩
  · exact fun r => Torus.coroot_expansion r.down
  · exact fun r t => Torus.corootWord_expansion k r.down t
  · exact fun _ t => Torus.supportCorootProduct_eq_one_iff k t
  · exact fun _ t => Torus.supportCorootProduct_eq_one_iff_roots k t
  · exact ⟨Torus.weights k, Torus.weights_generate k,
      Torus.supportCorootProduct_eq_one_iff_weights k⟩
  · intro r s a
    simpa only [Units.val_one, one_mul] using reflection_root k r s a
  · intro r s t
    simpa only [one_mul] using reflection_normalizer k r s t
end
end Triality.SimplyConnected.Pinning.ChevalleySource
