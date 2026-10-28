module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic.Reduction
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreCensus

/-!
# Identifying the original cubic core in the marked Tits Sylow

The source reduction supplies a marking of the original common Sylow such
that the pullback of O₂(YT) has index two and center of order at least four.
The finite Tits core census identifies that literal pullback with the comap
of O₂(second) along the fixed inclusion of the concrete Sylow. All original
source hypotheses, the index-five hypothesis and the first-endpoint
isomorphism are retained. No cubic reflection or whole-endpoint recognition
is assumed or asserted here.

Source: Aschbacher--Smith F.1.11--12, printed pp.262--264, and 14.2.20--21,
printed pp.988--989. The whole second-endpoint assembly is separate.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Tits.ExceptionalParabolics
variable {G : Type*} [Group G] [Finite G]

/-- The actual source two-core pulls back to the specified second Tits core. -/
theorem source_core_identification
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hfirst : Nonempty (Tits.ExceptionalParabolics.first ≃* H)) :
    ∃ σ : S ≃* (T : Subgroup G),
      coreInMarkedSylow T (sourceResidual M Mc ⊔ (T : Subgroup G)) le_sup_right σ =
        SecondRecognition.coreInSylow := by
  obtain ⟨σ, hiK, hzK⟩ :=
    source_core_input hG T hempty hM hu hmany hcard e H hH hi hfirst
  exact ⟨σ, SecondCoreCensus.eq_coreInSylow_of_index_two_of_center_card _ hiK hzK⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
