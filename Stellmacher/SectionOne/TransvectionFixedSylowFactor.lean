module

public import Stellmacher.SectionOne.FixedIndexTwoOffender
public import Stellmacher.SectionOne.OffenderActiveFactorSupport
public import Stellmacher.SectionOne.OneSevenFactorConjugation

/-!
# Selecting a Sylow-normalized factor from a fixed transvection

Under the faithful elementary-abelian action hypotheses of Section One,
suppose Y lies in a Sylow two-subgroup U, its full fixed space has index
two, and its action commutator is fixed by U. Then some raw factor from
Stellmacher (1.7) is normalized by U.

Quadraticity and faithfulness make Y elementary abelian, and the full
fixed index makes it a nontrivial offender. The proved local factor and
module decompositions select a nonidentity point in both its commutator
and a factor support. This point is U-fixed, so it also lies in every
U-conjugate of that support. Distinct raw factors have disjoint supports;
therefore every such conjugate factor equals the selected factor.

This is the intrinsic action input for (9.2). It asserts Sylow-normalization
only: full normality requires the independent odd-core supplement in the
local application. Every action here is the supplied ambient action.
Source: Stellmacher (1.7), printed p.19 (PDF page 9), and its application
in (9.2), printed p.48, of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne
universe u

private theorem factor_normalized_of_fixed_support_point
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (D T : Subgroup K)
    (hD : IsOneSevenFactor (V := V) D) (v : V)
    (hv : v ∈ commutatorAction D V) (hne : v ≠ 1)
    (hfix : v ∈ FixedPoints.subgroup T V) :
    T ≤ Subgroup.normalizer (D : Set K) := by
  intro g hg
  have hgfix : g • v = v := by
    rw [FixedPoints.mem_subgroup] at hfix
    exact hfix ⟨g, hg⟩
  have hDg := hD.conjBy D g
  have hvg : v ∈ commutatorAction (D.conjBy g) V := by
    rw [← RankOneThreeGroupAssembly.commutatorAction_conjBy D g]
    exact ⟨v, hv, hgfix⟩
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  by_contra hneq
  have hderived : (commutator (D.conjBy g)).map (D.conjBy g).subtype ≠
      (commutator D).map D.subtype := by
    intro heq
    exact hneq (oneSevenFactor_eq_of_derived_eq h _ _ hDg hD heq)
  have hdisj : Disjoint (commutatorAction (D.conjBy g) V)
      (commutatorAction D V) := by
    rw [oneSevenFactor_full_commutator_eq_derived _ hDg,
      oneSevenFactor_full_commutator_eq_derived D hD]
    exact omega_pair_action_disjoint h hDg.2.1 hD.2.1 hderived
      (oneSevenFactor_derived_le_threeCore _ hDg)
      (oneSevenFactor_derived_le_threeCore D hD) le_rfl
  exact hne (hdisj.le_bot ⟨hvg, hv⟩)

/-- Full fixed index two and a Sylow-fixed action commutator select a raw
one-seven factor normalized by that Sylow subgroup. -/
public theorem oneSeven_factor_of_fixed_index_two
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (U : Sylow 2 K) (Y : Subgroup K)
    (hYU : Y ≤ (U : Subgroup K))
    (hindex : Nat.card V = 2 * Nat.card (FixedPoints.subgroup Y V))
    (hfixed : commutatorAction Y V ≤ FixedPoints.subgroup (U : Subgroup K) V) :
    ∃ D : Subgroup K, IsOneSevenFactor (V := V) D ∧
      (U : Subgroup K) ≤ Subgroup.normalizer (D : Set K) := by
  obtain ⟨hY, hYne⟩ := oneA_of_fixed_index_two h U Y hYU hindex hfixed
  obtain ⟨D, hD, v, hne, hv, hvY⟩ :=
    oneSeven_factor_support_meets_offender h U Y hY hYne
  exact ⟨D, hD, factor_normalized_of_fixed_support_point h D U hD v hv hne (hfixed hvY)⟩

end Stellmacher.SectionOne
