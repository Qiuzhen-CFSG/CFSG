module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Preparation

/-!
# Independent local and representation inputs for 10.2.11

SeedAnalysis specifies the computations in the original X T and G_z ∩ M.
The remaining representation argument may use the proved central-core and
full-action reducedness conclusions explicitly. Neither proposition asserts
that these source obligations have been discharged.

Source: Aschbacher--Smith 10.1.3 and 10.2.11, printed pp.742,753--754.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

/-- Local seed calculations, before either reducedness or the V-core bound.
The normality clause is the consequence of X = O^{3'}(G_z ∩ M) on a
normal intermediate subgroup, not an assumption that X is normal in G_z. -/
structure SeedAnalysis (c : Configuration s a b) : Prop where
  core_bound : (centralizerSeed T L (a*b) ⊔ (T : Subgroup G)).pCoreIn 2 ≤
    (T : Subgroup G) ⊓ normalizer (L : Set G)
  commutator : ∀ R : Subgroup G, R ≤ (T : Subgroup G) →
    (T : Subgroup G) ≤ normalizer (R : Set G) →
    ¬ R ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) →
      ⁅centralizerSeed T L (a*b), R⁆ = centralizerSeed T L (a*b)
  normal_in_kernel : ∀ C : Subgroup G,
    C ≤ centralizer ({a*b} : Set G) ⊓ D.maximalLocal →
    centralizer ({a*b} : Set G) ≤ normalizer (C : Set G) →
    centralizerSeed T L (a*b) ≤ C →
      centralizer ({a*b} : Set G) ≤ normalizer (centralizerSeed T L (a*b) : Set G)
  fixes : centralizerSeed T L (a*b) ≤ centralizer
    ((zpowers a ⊔ zpowers b : Subgroup G) : Set G)
  generates : D.fullModule = ⁅D.fullModule, centralizerSeed T L (a*b)⁆ ⊔
    (zpowers a ⊔ zpowers b)

/-- The independent original local-group calculation. -/
def SeedAnalysisAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (a b : G) (c : Configuration s a b),
      SeedAnalysis c

/-- The final representation contradiction in 10.2.11(3). The independent
local calculation remains an explicit premise, allowing its producer to run
alongside this conditional consumer. Reducedness
belongs to the entire literal G_z action; it is not transferred to K_z T.
The conclusion states the centralization needed by the proved core reduction. -/
def FullActionCentralizationAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (a b : G) (c : Configuration s a b),
    SeedAnalysis c →
    centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2) →
    centralizerSeed T L (a*b) < componentSpan T L (a*b) →
    IsPReduced 2 ((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G))) →
    D.fullModule ≤ centralizer (centralizerModule a b : Set G)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced
