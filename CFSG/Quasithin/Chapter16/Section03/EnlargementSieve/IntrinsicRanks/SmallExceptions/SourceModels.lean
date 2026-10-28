module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.SmallExceptions
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.LiePairs.UnitaryExclusion

/-!
# Source quotient conventions for the exceptional enlargement cases

The field-pair table uses two-core quotients. E1 identifies those actual
cores with the centers of the two components; the explicit quotient
isomorphisms then supply the rank exclusions. For a full Rudvalis model,
the exact earlier 16.3.4 exclusion applies directly in the enlargement setup.

The G₂ exclusion uses the proved automorphism bound for the actual binary
derived group. The earlier 16.3.4 theorem remains an explicit input only
to the separate Rudvalis adapter.

Source: Aschbacher–Smith, 16.1.2(1), 16.1.7(3a,i), and 16.3.4,9,
printed pp.1170,1172,1178,1180.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.SmallExceptions
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The Sp₄(4) field pair, with the source's literal two-core quotients. -/
theorem exclude_simple_symplectic_four_source
    (he : HasEvenTypeCentralizers G)
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    [IsSimpleGroup (enlargement t L)]
    (hmodel : ClassicalGroup.IsPSp (enlargement t L ⧸ pCore 2 (enlargement t L)) 2 4)
    {D : Type*} [Group D] (hD : ClassicalGroup.IsPSp D 2 2)
    (eL : (L ⧸ pCore 2 L) ≃* commutator D) : False := by
  let eK := QuotientGroup.quotientMulEquivOfEq
    (he.component_center_eq_twoCore h.involution hK)
  let e := QuotientGroup.quotientMulEquivOfEq
    (he.component_center_eq_twoCore h.localSetup.involution h.localSetup.component)
  exact exclude_simple_symplectic_four_quotient h hs hK
    (hmodel.of_mulEquiv eK) hD (e.trans eL)

/-- The G₂(4) field pair, retaining both two-core quotients and the actual
binary derived carrier, with its numerical input explicit. -/
theorem exclude_simple_g2_four_source_of_bound
    (hAut : primeRank 2 (MulAut (commutator (Atlas.G2.Model (ZMod 2)))) ≤ 3)
    (he : HasEvenTypeCentralizers G)
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    [IsSimpleGroup (enlargement t L)]
    (hmodel : ClassificationModels.IsG2At
      (enlargement t L ⧸ pCore 2 (enlargement t L)) 4)
    {D : Type*} [Group D] (hD : ClassificationModels.IsG2At D 2)
    (eL : (L ⧸ pCore 2 L) ≃* commutator D) : False := by
  let eK := QuotientGroup.quotientMulEquivOfEq
    (he.component_center_eq_twoCore h.involution hK)
  let e := QuotientGroup.quotientMulEquivOfEq
    (he.component_center_eq_twoCore h.localSetup.involution h.localSetup.component)
  exact exclude_simple_g2_four_quotient_of_bound hAut h hs hK
    (hmodel.of_mulEquiv eK) hD (e.trans eL)

/-- The simple G₂(4) field-pair exclusion with the literal source two-core
quotients and no additional numerical premise. -/
theorem exclude_simple_g2_four_source
    (he : HasEvenTypeCentralizers G)
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    [IsSimpleGroup (enlargement t L)]
    (hmodel : ClassificationModels.IsG2At
      (enlargement t L ⧸ pCore 2 (enlargement t L)) 4)
    {D : Type*} [Group D] (hD : ClassificationModels.IsG2At D 2)
    (eL : (L ⧸ pCore 2 L) ≃* commutator D) : False :=
  exclude_simple_g2_four_source_of_bound g2_binary_derived_automorphism_two_rank
    he h hs hK hmodel hD eL

omit [Finite G] in
/-- Apply the precise earlier exclusion to the full simple Rudvalis model,
with all relative component and commutator hypotheses retained. -/
theorem exclude_simple_rudvalis
    (exclude : ∀ (J : Subgroup G) (a b : G),
      FourGroupTransfer.ExclusionSetup T z L J a b →
        ¬ FourGroupTransfer.IsExcludedSimple J)
    (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hL : ComponentTransfer.IsComponentIn L
      (ComponentTransfer.centralizerIn (enlargement t L) z))
    (hcomm : ⁅enlargement t L, zpowers z⁆ = enlargement t L)
    (eK : Nonempty (enlargement t L ≃* ClassificationModels.SporadicName.ru.Carrier)) :
    False :=
  exclude _ _ _ (LiePairs.unitary_exclusion_setup h hK hL hcomm)
    (Or.inr (Or.inr (Or.inr (Or.inr eK))))

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.SmallExceptions
