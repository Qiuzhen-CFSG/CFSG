module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.Comparison
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.SourceInputs

/-!
# The constructed rank-two A.3.18 application

Full Hypothesis 13.3.1 in the A₅ counterexample setting and the genuine
earlier local conclusions produce all application hypotheses for
H = KLᵥ and C = K.subgroupOf H. A.3.6 excludes the nonquasisimple cases
at three-rank two; A.3.12 and rigidity localize the C-component; the two
literal images of C/O₂(C) give the compatible central quotient comparison.

The seven-model list stays in the source input for the enclosing A.3.18
case analysis. The final theta identity and discharge of the earlier
source inputs belong to that enclosing owner. This module constructs
application data and makes no assumption of that data.
Source: Aschbacher–Smith, combined manuscript, 13.6.20, p.931;
A.3.18, pp.51–53; Hypothesis 13.3.1, p.884.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentSelection Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Constructed application hypotheses and compatible quotient comparison.
This is output data; no theorem below assumes a value of this structure. -/
structure ApplicationData (κ : GroupClass.{u}) (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) where
  actor_sqtk : IsSQTK κ (localActor K L v)
  component : (localComponent K L v).IsCComponent
  intrinsic_quasisimple : IsQuasisimple (K ⧸ pCore 2 K)
  intrinsic_center_rank : primeRank 3 (center (K ⧸ pCore 2 K)) ≤ 1
  component_rank : primeRank 3 (localComponent K L v) = 2
  local_quasisimple : IsQuasisimple (localComponent K L v ⧸ pCore 2 (localComponent K L v))
  local_center_rank : primeRank 3 (center (localComponent K L v ⧸ pCore 2 (localComponent K L v))) ≤ 1
  image_quasisimple : IsQuasisimple (localImage K L v)
  comparison : (localImage K L v ⧸ center (localImage K L v)) ≃*
    (plusImage K L T z v hL hz K ⧸ center (plusImage K L T z v hL hz K))
  compatibility : ∀ k : K,
    comparison (QuotientGroup.mk' (center (localImage K L v)) (toLocalImage K L v k)) =
      QuotientGroup.mk' (center (plusImage K L T z v hL hz K))
        (toPlusImage K L T z v hK hL hz k)

/-- Construct the exact A.3.18 hypotheses under the full §13.6 source setup.
Only the universal A.3.6 classification and A.3.12 containment clause remain
as earlier classification parameters. The enclosing source owner supplies
the genuine earlier local conclusions in d and performs the A.3.18 cases. -/
noncomputable def source_application
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
        ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
        ∀ (S : Sylow 2 X) (B : Subgroup X), B ∈ ChapterA.Section03.localCComponents S →
          ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    {T : Sylow 2 G} {K L : Subgroup G} {z v : G} (d : SourceInputs T K L z v) :
    ApplicationData KnownSimple.IsKnownSimple K L (T : Subgroup G) z v
      d.selected.1.1 d.normalizes_residual d.centralizes_z := by
  have hR := plus_twoCore_eq_bot_of_reduced K L (T : Subgroup G) z v
    d.normalizes_residual d.centralizes_z d.reduced_module
  obtain ⟨hq, hc⟩ := source_intrinsic_quasisimple d.standing.qtke hA36
    K L (T : Subgroup G) z v d.involution d.selected d.rank_two
  obtain ⟨hsq, hr, hqC, hcC⟩ := source_local_intrinsic d.standing.qtke hA36
    K L (T : Subgroup G) z v d.involution d.selected d.rank_two
  exact {
    actor_sqtk := hsq
    component := source_local_cComponent d.standing.qtke hA36 hA312
      K L (T : Subgroup G) z v d.involution d.selected d.rank_two
      d.sylow_centralizer d.normalizes_component d.normalizes_residual d.centralizes_z hR
    intrinsic_quasisimple := hq
    intrinsic_center_rank := hc
    component_rank := hr
    local_quasisimple := hqC
    local_center_rank := hcC
    image_quasisimple := source_localImage_quasisimple d.standing.qtke hA36 hA312
      K L (T : Subgroup G) z v d.involution d.selected d.rank_two
      d.sylow_centralizer d.normalizes_component d.normalizes_residual d.centralizes_z hR
    comparison := localPlusCentralQuotientEquiv d.standing.qtke hA36 hA312
      K L (T : Subgroup G) z v d.involution d.selected d.rank_two
      d.sylow_centralizer d.normalizes_component d.normalizes_residual d.centralizes_z hR
    compatibility := localPlusCentralQuotientEquiv_mk d.standing.qtke hA36 hA312
      K L (T : Subgroup G) z v d.involution d.selected d.rank_two
      d.sylow_centralizer d.normalizes_component d.normalizes_residual d.centralizes_z hR }

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
