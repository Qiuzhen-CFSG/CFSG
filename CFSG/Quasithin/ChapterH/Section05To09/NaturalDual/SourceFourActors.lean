module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors.ProofData
/-!
# H.9.3 on the original source group and module

The only input is `S : SourceSetup 4 M V` and the given `T : Sylow 2 M`.
`permutation` is the genuine exceptional S₈ comparison, with the layer and
both natural/dual summands marked by compatible group and linear maps.

* `outer_involution_catalogue` and `diagonalEquiv` give clauses (1–2),
  including actual relative centralizers and the literal equivariant map
  w ↦ w + t.w, whose image is both the fixed and displacement space.
* `actor_exhaustion`, `actor_conjugate_iff`, `actor_orbit` and
  `elementaryThompson_eq_A0` give clause (3) for the ORIGINAL Sylow T.
* `A0_parameters`, `A1_parameters`, `A1_transvection`, and `A2_parameters`
  give clauses (4–6), including the actual E.3.30 subgroup cores.
* `A2_three_transvections`, `A2_fixed_planes`, `A2_other_fixed`,
  `naturalB2_core`, `outerFixed_cores`, and `A2_mixed_eq_commutator` retain
  the proof data on p.392, including the quotient action on C_V(a).

The proofs choose an inner Sylow adjustment and transport the completed
coordinate calculations through the SAME source group/module equivalences.
No actor, marking, fixed-space, core, or comparison premise is assumed.
The original NaturalDual umbrella is left for the whole-H.9 assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3,
printed pp.391–392, PDF pp.402–403. The comparison uses the attributed
ATLAS port through `BinaryNaturalDual.FourActors.permutationEquiv`.
-/

public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 4 M V) (T : Sylow 2 M)

theorem permutation_mem_alternating (a : M) :
    permutation S T a ∈ alternatingGroup (Fin 8) ↔ a ∈ componentLayer M :=
  (BinaryNaturalDual.FourActors.permutationEquiv_mem_alternating _).trans (group_inner_iff S T a)

theorem permutation_transposition :
    permutation S T (transposition S T) = Theory.SpecificGroups.SymmetricEight.Involutions.onePair := by
  change BinaryNaturalDual.FourActors.permutationEquiv
    (group S T ((group S T).symm BinaryNaturalDual.FourActors.transposition)) = _
  rw [MulEquiv.apply_symm_apply, BinaryNaturalDual.FourActors.permutationEquiv_transposition]

theorem permutation_tripleTransposition :
    permutation S T (tripleTransposition S T) = Theory.SpecificGroups.SymmetricEight.Involutions.threePairs := by
  change BinaryNaturalDual.FourActors.permutationEquiv
    (group S T ((group S T).symm BinaryNaturalDual.FourActors.tripleTransposition)) = _
  rw [MulEquiv.apply_symm_apply, BinaryNaturalDual.FourActors.permutationEquiv_tripleTransposition]

theorem r_cycleType : (permutation S T (r S T)).cycleType = {2,2,2,2} := by
  change (BinaryNaturalDual.FourActors.permutationEquiv (group S T (r S T))).cycleType = _
  rw [r_map, BinaryNaturalDual.FourActors.permutationEquiv_r]
  exact Theory.SpecificGroups.SymmetricEight.Involutions.fourPairs_cycleType

/-- The native rank-one fixed space is the actual diagonal line. -/
theorem A1_fixed_line :
    S.fixed (A1 S T) = Submodule.span (ZMod 2)
      {((naturalCoordinates S T).symm (![1,1,0,0] : BinaryNaturalDual.FourActors.X) : V) +
        S.representation (transposition S T)
          ((naturalCoordinates S T).symm (![1,1,0,0] : BinaryNaturalDual.FourActors.X) : V)} := by
  apply Submodule.map_injective_of_injective (coordinates S T).injective
  rw [fixed_map, actor_map, Submodule.map_span, Set.image_singleton]
  simp only [LinearEquiv.coe_coe, map_add, equivariant, natural_marking, LinearEquiv.apply_symm_apply]
  change BinaryNaturalDual.FourActors.actorFixed _ BinaryNaturalDual.FourActors.A1 =
    Submodule.span (ZMod 2) {(_,0) +
      (AutomorphismModel.coordinateAction S.degree).representation
        (group S T ((group S T).symm BinaryNaturalDual.FourActors.transposition)) (_,0)}
  rw [MulEquiv.apply_symm_apply]
  exact BinaryNaturalDual.FourActors.Parameters.A1_fixed_line _

/-- The native core can also be read as the literal sum of subgroups of V. -/
theorem A2_subgroup_core (a : M) (ha : a ∈ A2 S T) (haB : a ∉ B2 S T) :
    ChapterE.dualGeneratedCore (multiplicativeAction (S.representation.comp (A2 S T).subtype)) 2 =
      subgroupOrderIso (S.fixed (B2 S T)) ⊔ subgroupOrderIso (elementFixed S a) := by
  rw [(A2_parameters S T a ha haB).2.2.2.2, OrderIso.map_sup]
end CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
