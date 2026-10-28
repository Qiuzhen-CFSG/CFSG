module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis.CentralizerGeometry.Transport
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis.CentralizerGeometry.Series

/-!
# The Rudvalis local block cover for 2.3.9(7)

The actual max4 conjugate over the component Sylow, together with the fixed
subgroup of the original inner involution, generates the Rudvalis quotient.
Central-cover transport and the component orbit give a local overgroup of the
supplied S with nontrivial self-centralizing two-core. Its relative factor
series has only two-group and simple order-168 factors. The proved
`LocalFactorSeries.not_chiZeroBlockIn` excludes all relevant subnormal blocks.

The exported theorem constructs the literal `CentralizerBlockCover` from h
and d alone, preserving a possible central two-kernel and component permutations.
It does not require the stronger old `LocalGeometry` generator conditions.
The parent Rudvalis owner retains the final sporadic-case assembly.

Source: Aschbacher–Smith 2.3.9(7), printed p.526; GLS3 Table 5.3r and its
max4 justification, printed pp.291–292.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase.CentralizerGeometry
open Subgroup Theory.GroupTheory

/-- The Rudvalis local cover in the source setup of 2.3.9(7), with its literal
two-core quotient, original involution action and supplied Sylow subgroup. -/
theorem nonempty_centralizerBlockCover {G : Type*} [Group G]
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .ru) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) := by
  obtain ⟨K, hgen, hwithin, heven, ⟨c⟩⟩ := exists_local_with_max4_cover h d
  refine ⟨{ locals := {K}, generated := ?_, within := ?_, even := ?_, obstruction := ?_ }⟩
  · simpa only [sSup_singleton] using hgen
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    exact hwithin
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    exact heven
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    intro B hb _
    exact ((max4_cover_series c).not_chiZeroBlockIn B hb).elim

end CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase.CentralizerGeometry

end
