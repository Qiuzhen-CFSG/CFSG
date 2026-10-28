module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullReeExclusion
public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.Complete

/-!
# Compatible Parrott generators in the original marked Tits branch

The supplied local inputs suffice for the complete generator construction:
the derived-core normalizer identity and the second-normalizer solvability
replace every use of the ambient N₂ condition. The construction first chooses
and normalizes Sylow generators, extends them to the first centralizer, and
then normalizes the second-normalizer frame against that same centralizer.
The literal supplied second elementary subgroup, Sylow subgroup, t and v
are retained through the parameter n. All generation, order, conjugacy and
equation fields (1)–(26) are constructed.

This discharges `hgenerators` in
`source_tits_recognition_of_local_constructions`. The second-centralizer
construction and final ambient recognition remain with that assembly.
Source: Parrott (1972), §3, printed pp.678–682; Aschbacher–Smith 14.2.22,
printed p.989, and F.4.31, pp.290–291.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel : ChapterF.GreenBook.IsAtlasTitsAmalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right))

include hG hempty hM hu hmany hcard e hH hmodel

-- Retain the complete marked-source signature expected by the assembly.
-- The local construction itself needs only the supplied local inputs.
set_option linter.unusedSectionVars false in
/-- Compatible generators for every supplied local configuration in the original
marked Tits branch. No ambient N₂, braid or generation assumption is used. -/
theorem source_tits_compatible_generators
    (z : G) (_hz : zpowers z = centralInvolutions T)
    (hp : Recognition.ParrottCentralizerHypotheses z)
    (hlocal : Recognition.ParrottLocalInputs z)
    (d : Recognition.ParrottSecondElementaryData z)
    (n : Recognition.ParrottNormalizerFusionData d) :
    Nonempty (Σ f : Recognition.ParrottCentralizerGeneratorData n,
      Recognition.ParrottNormalizerGeneratorData f) := by
  let : IsSimpleGroup G := hG.simple
  have hns : ¬ Group.IsSolvable G := fun hs =>
    hG.nonabelian (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))
  exact n.exists_local_generators_of_local_inputs hns hlocal hp

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
