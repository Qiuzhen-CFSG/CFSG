module

public import Stellmacher.SectionOne.FixedIndexTwoOffender
public import Stellmacher.SectionOne.OffenderActiveFactorSupport
public import Stellmacher.SectionOne.OneSevenFactorConjugation
public import Theory.GroupAction.FourElementInvolutionLines

/-!
# Rank-one action support selection

The action commutator of a rank-one offender lies in a unique raw factor
support from (1.7). These supports are invariant under the odd core, and
distinct conjugates are disjoint. Pulling back along a quotient map turns
that disjointness into intersection equal to the kernel.

These are action-algebra inputs to the support lift in (9.5), not an
existence theorem for the ambient Section Nine support seed.
-/

namespace Stellmacher.SectionOne

universe u

public theorem oneSevenFactor_support_disjoint_of_ne
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (first second : Subgroup K)
    (hfirst : IsOneSevenFactor (V := V) first)
    (hsecond : IsOneSevenFactor (V := V) second) (hne : first ≠ second) :
    Disjoint (commutatorAction first V) (commutatorAction second V) := by
  have hderived : (commutator first).map first.subtype ≠
      (commutator second).map second.subtype := by
    intro heq
    exact hne (oneSevenFactor_eq_of_derived_eq hyp first second hfirst hsecond heq)
  rw [oneSevenFactor_full_commutator_eq_derived first hfirst,
    oneSevenFactor_full_commutator_eq_derived second hsecond]
  exact omega_pair_action_disjoint hyp hfirst.2.1 hsecond.2.1 hderived
    (oneSevenFactor_derived_le_threeCore first hfirst)
    (oneSevenFactor_derived_le_threeCore second hsecond) le_rfl

public theorem oneSeven_rank_one_offender_support
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (sylow : Sylow 2 K) (actors : Subgroup K)
    (hoffender : oneA (V := V) (sylow : Subgroup K) actors)
    (hne : actors ≠ ⊥) (hrank : Nat.card (commutatorAction actors V) = 2) :
    ∃! factor : Subgroup K, IsOneSevenFactor (V := V) factor ∧
      commutatorAction actors V ≤ commutatorAction factor V := by
  obtain ⟨factor, hfactor, vector, hvne, hvfactor, hvactors⟩ :=
    oneSeven_factor_support_meets_offender hyp sylow actors hoffender hne
  have hcontains : commutatorAction actors V ≤ commutatorAction factor V := by
    intro point hpoint
    have hgen := mem_zpowers_of_prime_card hrank
      (g := (⟨vector, hvactors⟩ : commutatorAction actors V))
      (g' := (⟨point, hpoint⟩ : commutatorAction actors V))
      (fun heq => hvne (congrArg Subtype.val heq))
    obtain ⟨power, hpower⟩ := hgen
    have heq : vector ^ power = point := congrArg Subtype.val hpower
    rw [← heq]
    exact (commutatorAction factor V).zpow_mem hvfactor power
  refine ⟨factor, ⟨hfactor, hcontains⟩, ?_⟩
  intro other hother
  by_contra hneq
  have hdisjoint := oneSevenFactor_support_disjoint_of_ne hyp other factor
    hother.1 hfactor hneq
  exact hvne (hdisjoint.le_bot ⟨hother.2 hvactors, hvfactor⟩)

public theorem oneSeven_order_two_rank_one_support
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [Nontrivial V] [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (sylow : Sylow 2 K) (actors : Subgroup K)
    (hle : actors ≤ (sylow : Subgroup K)) (hcard : Nat.card actors = 2)
    (hrank : Nat.card (commutatorAction actors V) = 2) :
    ∃! factor : Subgroup K, IsOneSevenFactor (V := V) factor ∧
      commutatorAction actors V ≤ commutatorAction factor V := by
  obtain ⟨actor, hactor, _⟩ := (Nat.card_eq_two_iff' (1 : actors)).mp hcard
  have hsquare : actor ^ 2 = 1 := by
    simpa only [hcard] using (pow_card_eq_one' (x := actor))
  obtain ⟨hproduct, hfixed⟩ :=
    card_two_action_fixed_commutator_card_data (U := V) actor ⟨hactor, hsquare⟩ hcard
  have hindex : Nat.card V = 2 * Nat.card (FixedPoints.subgroup actors V) := by
    simpa only [hrank, Nat.mul_comm] using hproduct
  obtain ⟨hoffender, hne⟩ :=
    oneA_of_quadratic_fixed_index_two hyp sylow actors hle hindex hfixed
  exact oneSeven_rank_one_offender_support hyp sylow actors hoffender hne hrank

public theorem oneSevenFactor_support_oddCore_invariant
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [MulDistribMulAction K V] (factor : Subgroup K)
    (hfactor : IsOneSevenFactor (V := V) factor) :
    IsInvariant (oddCore K) V (commutatorAction factor V) := by
  apply commutatorAction_isInvariant_of_normalizing_actor
  exact (show oddCore K ≤ oddCore K ⊔ factor from le_sup_left).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mp hfactor.2.2.2)

public theorem oneSevenFactor_support_conjugate_inf
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (factor : Subgroup K)
    (hfactor : IsOneSevenFactor (V := V) factor) (actor : K)
    (hne : commutatorAction factor V ≠ (commutatorAction factor V).map
      (MulDistribMulAction.toMulAut K V actor).toMonoidHom) :
    commutatorAction factor V ⊓ (commutatorAction factor V).map
      (MulDistribMulAction.toMulAut K V actor).toMonoidHom = ⊥ := by
  rw [RankOneThreeGroupAssembly.commutatorAction_conjBy] at hne ⊢
  apply (oneSevenFactor_support_disjoint_of_ne hyp factor (factor.conjBy actor)
    hfactor (hfactor.conjBy factor actor) ?_).eq_bot
  intro heq
  exact hne (congrArg (fun subgroup : Subgroup K => commutatorAction subgroup V) heq)

public theorem oneSevenFactor_lifted_support_conjugate_inf
    {K V L : Type u} [Group K] [Group V] [Group L] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (factor : Subgroup K)
    (hfactor : IsOneSevenFactor (V := V) factor) (actor : K) (projection : L →* V)
    (hne : (commutatorAction factor V).comap projection ≠
      ((commutatorAction factor V).map
        (MulDistribMulAction.toMulAut K V actor).toMonoidHom).comap projection) :
    (commutatorAction factor V).comap projection ⊓
      ((commutatorAction factor V).map
        (MulDistribMulAction.toMulAut K V actor).toMonoidHom).comap projection =
      projection.ker := by
  rw [← Subgroup.comap_inf]
  have hdistinct : commutatorAction factor V ≠ (commutatorAction factor V).map
      (MulDistribMulAction.toMulAut K V actor).toMonoidHom := by
    intro heq
    exact hne (congrArg (fun subgroup => subgroup.comap projection) heq)
  rw [oneSevenFactor_support_conjugate_inf hyp factor hfactor actor hdistinct]
  rfl

end Stellmacher.SectionOne
