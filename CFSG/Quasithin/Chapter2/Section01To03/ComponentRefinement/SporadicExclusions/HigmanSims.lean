module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HigmanSims.SectionOrders
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HigmanSims.Seed
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HigmanSims.Transport
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete

/-!
# The Higman–Sims branch of the sporadic block calculation

Source: Aschbacher–Smith, 2.3.9(7), printed p.526.

The concrete normalizer of the characteristic elementary eight in a Sylow
two-subgroup of the exact degree-100 HS carrier has a self-centralizing
two-core and actual `SL₃(2)` quotient. Its full inverse image, adjoined to the
supplied S, lies in L ∨ S and has a nontrivial self-centralizing two-core.
The component-orbit section is a direct power of `SL₃(2)`, whose subnormal
section orders exclude every χ₀ block. Lifting the fixed-subgroup two-residual
gives generation together with the actual C_G(z), retaining the full central
two-kernel even when S permutes components.

The theorem below discharges the geometry premise of the cover construction
using the proved concrete normalizer calculation (GLS3, Table 5.3m and p.306).
It supplies the HS cover to the parent sporadic-exclusion assembly with no
additional geometry, splitting, or centerlessness hypotheses on L.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The HS local block cover in the proof of 2.3.9(7), with all concrete
normalizer, central-cover, component-orbit and block calculations supplied. -/
theorem nonempty_centralizerBlockCover (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) := by
  obtain ⟨g⟩ := localGeometry_of_intrinsicGeometry
    Sporadic.LeechRelated.HS.BlockNormalizer.geometry h d
  exact ⟨centralizerBlockCover_of_geometry h d g⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims
