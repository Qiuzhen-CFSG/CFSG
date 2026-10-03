module
public import Stellmacher.SectionOne.OneSevenFixedSpaceNormalizer
public import Mathlib.GroupTheory.Index

/-!
# Arbitrary actors fixing a support line act modulo that line

Under the exact Section One hypotheses, let D be a one-seven factor and
R an order-two subgroup of its four-element support. Any ambient actor
fixing R pointwise sends every vector of that support to its own coset
modulo R. No Sylow, J-membership, or actor-order restriction is needed.

A nonidentity fixed vector belongs to both the support of D and the support
of its conjugate factor. Distinct factors have disjoint supports by the
three-core action decomposition and factor uniqueness, so the actor
normalizes D and preserves its support. The line has index two there. The
actor preserves membership in the line, and any two vectors outside an
index-two subgroup have their quotient inside it. This gives the required
action-difference bound directly without introducing a quotient action.

This proves the natural-support step in Stellmacher (8.4)(9), Journal of
Algebra 190 (1997), pp39--40, refs/files/stellmacher-n-group.pdf. The factor
normalization argument is the point-stabilizer part of the fixed-space
normalizer theorem used in (1.7), whose public API is unchanged.
-/

namespace Stellmacher.SectionOne
universe u

private theorem fixed_support_point_normalizes
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (D : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D)
    (g : G) (v : V) (hv : v ∈ commutatorAction D V)
    (hne : v ≠ 1) (hfix : g • v = v) : D.conjBy g = D := by
  have hDg := hD.conjBy D g
  have hvg : v ∈ commutatorAction (D.conjBy g) V := by
    rw [← RankOneThreeGroupAssembly.commutatorAction_conjBy D g]
    exact ⟨v,hv,hfix⟩
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
  exact hne (hdisj.le_bot ⟨hvg,hv⟩)

public theorem oneSevenFactor_fixed_line_control
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (D : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D)
    (R : Subgroup V) (hRU : R ≤ commutatorAction D V) (hR : Nat.card R = 2)
    (g : G) (hfix : ∀ r ∈ R, g • r = r) :
    ∀ v ∈ commutatorAction D V, v⁻¹ * (g • v) ∈ R := by
  classical
  let U := commutatorAction D V
  have hRne : R ≠ ⊥ := by
    intro he
    have hh := Subgroup.card_eq_one.mpr he
    omega
  obtain ⟨r,hrne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
  have hDg : D.conjBy g = D := fixed_support_point_normalizes h D hD g r
    (hRU r.property) (fun hh => hrne (Subtype.ext hh)) (hfix r r.property)
  have hUinv : ∀ v ∈ U, g • v ∈ U := by
    intro v hv
    have hm : g • v ∈ commutatorAction (D.conjBy g) V := by
      rw [← RankOneThreeGroupAssembly.commutatorAction_conjBy D g]
      exact ⟨v,hv,rfl⟩
    rw [hDg] at hm
    exact hm
  let R0 := R.subgroupOf U
  have hidx : R0.index = 2 := by
    have hh := R0.card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv,hR,
      show Nat.card U = 4 from hD.2.2.1] at hh
    omega
  intro v hv
  have hiff : g • v ∈ R ↔ v ∈ R := by
    constructor
    · intro hg
      have hh : g • (g • v) = g • v := hfix _ hg
      exact (MulAction.injective g hh) ▸ hg
    · intro hh
      rw [hfix v hh]
      exact hh
  have hm : (⟨v,hv⟩ : U)⁻¹ * ⟨g • v,hUinv v hv⟩ ∈ R0 := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    change v⁻¹ ∈ R ↔ g • v ∈ R
    exact R.inv_mem_iff.trans hiff.symm
  exact hm

end Stellmacher.SectionOne
