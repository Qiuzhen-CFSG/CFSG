module

public import Stellmacher.SectionOne.OneSevenFactorPair
public import Stellmacher.SectionOne.OneSevenFactorConjugation
public import Theory.GroupAction.NormalizingActor

/-!
# Fixed-space stabilizers normalize one-seven factors

If a two-subgroup normalizes a one-seven factor, its action on the factor's
four-element support has a nonidentity fixed point, by the fixed-point
congruence for two-group actions. Every pointwise fixer of the ambient fixed
space fixes this point. The conjugate factor therefore has a support meeting
the original support nontrivially. Lemma (1.4) and uniqueness from the derived
C3 subgroup force the two factors to coincide.

This gives the factor-normalization step for the Baumann subgroup in the
last paragraph of Stellmacher (1.7), journal page 19,
refs/latex/stellmacher-n-group.tex. The two-subgroup need not be elementary
abelian or Sylow; only its normalization of the given factor is used.
-/

namespace Stellmacher.SectionOne
universe u

public theorem oneSevenFactor_fixedSpace_normalizes
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (D T : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) (hT : IsPGroup 2 T)
    (hnorm : T ≤ Subgroup.normalizer (D : Set G)) :
    fixingSubgroup G (FixedPoints.subgroup T V : Set V) ≤
      Subgroup.normalizer (D : Set G) := by
  let U : Subgroup V := commutatorAction D V
  let _ : IsInvariant T V U :=
    _root_.commutatorAction_isInvariant_of_normalizing_actor T D hnorm
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiv : 2 ∣ Nat.card U := by rw [show Nat.card U = 4 from hD.2.2.1]; decide
  have hone : (1 : U) ∈ MulAction.fixedPoints T U := by
    rw [MulAction.mem_fixedPoints]
    intro t
    exact smul_one t
  obtain ⟨v, hv, hne⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdiv hone
  have hvfix : (v : V) ∈ FixedPoints.subgroup T V := by
    rw [FixedPoints.mem_subgroup]
    intro t
    exact congrArg Subtype.val (hv t)
  intro g hg
  have hgfix : g • (v : V) = (v : V) :=
    (mem_fixingSubgroup_iff (M := G)).mp hg v hvfix
  have hDg := hD.conjBy D g
  have hvg : (v : V) ∈ commutatorAction (D.conjBy g) V := by
    rw [← RankOneThreeGroupAssembly.commutatorAction_conjBy D g]
    exact ⟨v, v.property, hgfix⟩
  have heq : D.conjBy g = D := by
    by_contra hneq
    have hderived : (commutator (D.conjBy g)).map (D.conjBy g).subtype ≠
        (commutator D).map D.subtype := by
      intro heq
      exact hneq (oneSevenFactor_eq_of_derived_eq h _ _ hDg hD heq)
    have hdisj : Disjoint (commutatorAction (D.conjBy g) V) (commutatorAction D V) := by
      rw [oneSevenFactor_full_commutator_eq_derived _ hDg,
        oneSevenFactor_full_commutator_eq_derived D hD]
      exact omega_pair_action_disjoint h hDg.2.1 hD.2.1 hderived
        (oneSevenFactor_derived_le_threeCore _ hDg)
        (oneSevenFactor_derived_le_threeCore D hD) le_rfl
    have hvone : (v : V) = 1 := hdisj.le_bot ⟨hvg, v.property⟩
    exact hne (Subtype.ext hvone.symm)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end Stellmacher.SectionOne

