module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullReeExclusion
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsSourceFusion
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsGenerators
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsSecondCentralizer
public import CFSG.Quasithin.ClassificationModels
public import Stellmacher.Recognition.Parrott.RecognitionFromLocalInputs

/-!
# Ambient recognition in the original marked Tits branch

Original 14.2.21 identifies the first marked parabolic with the full central
involution centralizer. The source hypotheses construct Parrott's local inputs
and the second elementary subgroup with its normalizer and fusion data.
Compatible generators and the two-transfer calculation identify the full
second centralizer for those same witnesses. The local inputs prove exponent
four of its two-core, completing the presentation relations and ambient
recognition.

`source_tits_recognition` retains the original source hypotheses and the
explicit compatible Tits marking, and has no further construction premises.
`source_tits_theoremE` supplies the actual Tits alternative of Theorem E.
The conditional interfaces are retained for existing callers. Construction
of the compatible marking remains with the quintic enumeration owner.

Source: Aschbacher--Smith 14.2.22, printed p.989, and F.4.31, pp.290–291;
Parrott (1972), §§3–6, printed pp.678–684.
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
    (hgenerators : ∀ z : G, zpowers z = centralInvolutions T →
      Recognition.ParrottCentralizerHypotheses z → Recognition.ParrottLocalInputs z →
      ∀ (d : Recognition.ParrottSecondElementaryData z)
        (n : Recognition.ParrottNormalizerFusionData d),
        Nonempty (Σ f : Recognition.ParrottCentralizerGeneratorData n,
          Recognition.ParrottNormalizerGeneratorData f))
    (hcentralizer : ∀ z : G, zpowers z = centralInvolutions T →
      Recognition.ParrottCentralizerHypotheses z → Recognition.ParrottLocalInputs z →
      ∀ (d : Recognition.ParrottSecondElementaryData z)
        (n : Recognition.ParrottNormalizerFusionData d),
        Recognition.ParrottSecondCentralizerData n)

include hG hempty hM hu hmany hcard e hH hmodel hgenerators hcentralizer

/-- Conditional ambient recognition in the original marked Tits branch.
Both construction inputs apply to the same actual source witnesses; no
exponent, ambient generation, or N₂ premise remains. -/
theorem source_tits_recognition_of_local_constructions :
    Nonempty (G ≃* Tits.ParrottGroup) := by
  obtain ⟨z, hz, hp, hlocal, d, ⟨n⟩⟩ := source_tits_normalizer_fusion
    hG T hempty hM hu hmany hcard e H hH ⟨hmodel.some.left.symm⟩
  obtain ⟨⟨f, k⟩⟩ := hgenerators z hz hp hlocal d n
  exact k.nonempty_equiv_tits_of_local_inputs hp hlocal
    (hcentralizer z hz hp hlocal d n)

/-- The conditional source recognition supplies the literal Tits alternative
of Theorem E, through the ambient equivalence with the certified carrier. -/
theorem source_tits_theoremE_of_local_constructions :
    ClassificationModels.IsTheoremEModel G := by
  exact .tits (source_tits_recognition_of_local_constructions
    hG T hempty hM hu hmany hcard e H hH hmodel hgenerators hcentralizer)

omit hgenerators hcentralizer in
/-- Ambient recognition from the original source hypotheses and the compatible
Tits marking. The actual generators and full second centralizer are constructed. -/
theorem source_tits_recognition :
    Nonempty (G ≃* Tits.ParrottGroup) := by
  exact source_tits_recognition_of_local_constructions
    hG T hempty hM hu hmany hcard e H hH hmodel
    (source_tits_compatible_generators hG T hempty hM hu hmany hcard e H hH hmodel)
    (source_tits_second_centralizer hG T hempty hM hu hmany hcard e H hH hmodel)

omit hgenerators hcentralizer in
/-- The marked Tits branch supplies the actual Tits alternative of Theorem E. -/
theorem source_tits_theoremE : ClassificationModels.IsTheoremEModel G := by
  exact .tits (source_tits_recognition hG T hempty hM hu hmany hcard e H hH hmodel)

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
