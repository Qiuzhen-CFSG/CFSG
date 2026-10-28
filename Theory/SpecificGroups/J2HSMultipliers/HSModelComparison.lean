module

public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSimsSimplicity
public import Theory.SpecificGroups.J2HSMultipliers.HSModelComparison.WittGraph
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.GraphOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.Covering

/-!
# Identification of the permutation and Leech models of Higman–Sims

A checked graph isomorphism conjugates the faithful Leech action into the
full automorphism group of the permutation graph. That graph group has order
at most twice the order of the published permutation carrier. Consequently
the perfect Leech image lies in the permutation carrier; their equal orders
then give equality. This constructs a multiplicative equivalence retaining
the literal graph action, including the two published generator actions.

Simplicity and perfectness transport along this equivalence. The center is
trivial, so the finite permutation carrier receives `IsQuasisimple`, as
required by the HS covering and multiplier calculations in Aschbacher–Smith,
I.1.3(1), printed p.407. No multiplier assertion is made here.

Sources: ATLAS `HSG1-p100B0`, with the inverse-generator convention of
`LeechRelated/AtlasCarriers/HS.lean`, and Gerald Höhn's marked Leech triangle
construction, ATLAS revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
The imported ATLAS sources retain their attribution and license in
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section

noncomputable section
namespace Sporadic.LeechRelated.HS.ModelComparison
open NormalizerIndex
open Atlas.Sporadic.HigmanSims (Model Points)

variable (e : permutationGraph ≃g Atlas.Sporadic.HigmanSims.graph)

def leechPermutation : Model →* Equiv.Perm (Fin 100) :=
  e.toEquiv.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom Model Points)

@[simp] theorem leechPermutation_apply (g : Model) (x : Fin 100) :
    leechPermutation e g x = e.symm (g • e x) := rfl

theorem leechPermutation_mem (g : Model) : leechPermutation e g ∈ graphGroup := by
  intro x y
  change permutationGraph.Adj (e.symm (g • e x)) (e.symm (g • e y)) ↔
    permutationGraph.Adj x y
  exact (e.symm.map_rel_iff).trans
    ((Atlas.Sporadic.HigmanSims.graph_action_preserves g (e x) (e y)).trans e.map_rel_iff)

def leechAction : Model →* graphGroup :=
  (leechPermutation e).codRestrict graphGroup (leechPermutation_mem e)

theorem leechAction_injective : Function.Injective (leechAction e) := by
  let := Atlas.Conway.hs_graph_faithful
  intro g h he
  apply (MulAction.toPerm_injective (β := Points))
  apply e.toEquiv.symm.permCongrHom.injective
  exact congrArg Subtype.val he

abbrev permutationSubgroup : Subgroup graphGroup := generated.subgroupOf graphGroup

theorem permutationSubgroup_card : Nat.card permutationSubgroup = 44352000 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe generated_le_graphGroup).toEquiv).trans
    card_carrier

theorem permutationSubgroup_index_le : permutationSubgroup.index ≤ 2 := by
  have h := permutationSubgroup.index_mul_card
  rw [permutationSubgroup_card] at h
  have hb := graphGroup_card_le
  omega

theorem leechAction_range : (leechAction e).range = permutationSubgroup := by
  let := Atlas.Sporadic.HigmanSims.perfect
  let := Group.IsPerfect.range (leechAction e)
  apply Subgroup.eq_of_le_of_card_ge
    (Subgroup.le_of_isPerfect_of_index_le_two _ _ permutationSubgroup_index_le)
  rw [permutationSubgroup_card,
    ← Nat.card_congr (MonoidHom.ofInjective (leechAction_injective e)).toEquiv,
    Atlas.Sporadic.HigmanSims.card]

def comparisonOfGraphEquiv : Carrier ≃* Model :=
  (Subgroup.subgroupOfEquivOfLe generated_le_graphGroup).symm.trans
    ((MulEquiv.subgroupCongr (leechAction_range e).symm).trans
      (MonoidHom.ofInjective (leechAction_injective e)).symm)

theorem comparisonOfGraphEquiv_compatible (g : Carrier) (x : Fin 100) :
    comparisonOfGraphEquiv e g • e x = e (g.val x) := by
  have he : leechAction e (comparisonOfGraphEquiv e g) =
      (⟨g.val, generated_le_graphGroup g.property⟩ : graphGroup) := by
    change (leechAction e) ((MonoidHom.ofInjective (leechAction_injective e)).symm _) = _
    exact MonoidHom.apply_ofInjective_symm _ _
  have hx := congrArg (fun k : graphGroup => k.val x) he
  change e.symm (comparisonOfGraphEquiv e g • e x) = g.val x at hx
  exact e.symm.injective (hx.trans (e.symm_apply_apply _).symm)

include e

theorem permutation_simple_of_graphEquiv : IsSimpleGroup Carrier := by
  let := Atlas.Sporadic.HigmanSims.isSimpleGroup
  exact (comparisonOfGraphEquiv e).isSimpleGroup

theorem permutation_perfect_of_graphEquiv : Group.IsPerfect Carrier := by
  let := Atlas.Sporadic.HigmanSims.perfect
  exact Group.IsPerfect.ofSurjective (f := (comparisonOfGraphEquiv e).symm.toMonoidHom)
    (comparisonOfGraphEquiv e).symm.surjective

theorem permutation_quasisimple_of_graphEquiv : Theory.GroupTheory.IsQuasisimple Carrier := by
  let := permutation_simple_of_graphEquiv e
  let := permutation_perfect_of_graphEquiv e
  have hz : Subgroup.center Carrier = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative Carrier (Subgroup.center_eq_top_iff.mp h))
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup }
omit e

/-- The actual multiplicative equivalence from the published permutation
carrier to the pointwise stabilizer of the marked Leech triangle. -/
def comparison : Carrier ≃* Model := comparisonOfGraphEquiv WittCertificate.graphEquiv

/-- Compatibility with the full defining permutation action, under the
explicit checked graph identification. -/
theorem comparison_compatible (g : Carrier) (x : Fin 100) :
    comparison g • WittCertificate.graphEquiv x = WittCertificate.graphEquiv (g.val x) :=
  comparisonOfGraphEquiv_compatible WittCertificate.graphEquiv g x

/-- In particular the first published generator acts by its specified permutation. -/
theorem comparison_generatorA (x : Fin 100) :
    comparison ⟨generatorA, Subgroup.subset_closure (by simp)⟩ •
      WittCertificate.graphEquiv x = WittCertificate.graphEquiv (generatorA x) :=
  comparison_compatible _ x

/-- In particular the second published generator acts by its specified permutation. -/
theorem comparison_generatorB (x : Fin 100) :
    comparison ⟨generatorB, Subgroup.subset_closure (by simp)⟩ •
      WittCertificate.graphEquiv x = WittCertificate.graphEquiv (generatorB x) :=
  comparison_compatible _ x

instance permutation_simple : IsSimpleGroup Carrier :=
  permutation_simple_of_graphEquiv WittCertificate.graphEquiv

instance permutation_perfect : Group.IsPerfect Carrier :=
  permutation_perfect_of_graphEquiv WittCertificate.graphEquiv

/-- Together with the existing finite permutation-carrier instance, this
supplies the base hypotheses for the HS covering and multiplier arguments. -/
instance permutation_quasisimple : Theory.GroupTheory.IsQuasisimple Carrier :=
  permutation_quasisimple_of_graphEquiv WittCertificate.graphEquiv

end Sporadic.LeechRelated.HS.ModelComparison
