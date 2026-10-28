module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsSourceSeed
public import Stellmacher.Recognition.Parrott.LocalNormalizer.Fusion

/-!
# The actual normalizer and involution fusion in the original Tits branch

The original source hypotheses supply Parrott's local inputs. The local
normalizer theorem then constructs the second elementary subgroup together
with its full normalizer, core, omega and two-class fusion data. All these
witnesses belong to the original ambient group and use the same central
involution, which generates the prescribed Sylow omega-center.

This removes the global N₂ premise from this stage of the source application.
Identification of the second full involution centralizer and construction of
the compatible presentation generators are still needed for recognition.

Source: Aschbacher--Smith 14.2.22, printed p.989; Parrott (1972), Lemmas 5--6,
printed pp.675--678.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The full normalizer and fusion witnesses follow from the original source
marking, without an N₂ or additional local-solvability hypothesis. -/
theorem source_tits_normalizer_fusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel : Nonempty (Tits.ExceptionalParabolics.first ≃* H)) :
    ∃ z : G, zpowers z = centralInvolutions T ∧
      Recognition.ParrottCentralizerHypotheses z ∧ Recognition.ParrottLocalInputs z ∧
      ∃ d : Recognition.ParrottSecondElementaryData z,
        Nonempty (Recognition.ParrottNormalizerFusionData d) := by
  let : IsSimpleGroup G := hG.simple
  have hns : ¬ Group.IsSolvable G := fun hs =>
    hG.nonabelian (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))
  obtain ⟨z,hz,hp,hlocal⟩ := source_tits_local_inputs
    hG T hempty hM hu hmany hcard e H hH hmodel
  exact ⟨z,hz,hp,hlocal,
    Recognition.parrott_normalizer_fusion_exists_of_local_inputs hns hp hlocal⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
