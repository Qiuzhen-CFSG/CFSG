module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullReeExclusion
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsSourceFusion

/-!
# From the marked quintic alternatives to the actual Tits fusion data

The original centralizer argument excludes the full binary Ree amalgam.
Rigidity identifies the two surviving parabolics with Mc and M. Transport
along the compatible Tits marking gives the genuine Sz(2) first quotient;
the original source then supplies Parrott's normalizer and fusion witnesses.

The marked enumeration is an explicit input to this reduction. Neither it
nor ambient Tits recognition is asserted here. In particular the printed
D₁₀ quotient in F.1.12(I)(9) is not used: the concrete Tits first quotient
is Sz(2), as required by the conclusion of original 14.2.20(1).

Source: Aschbacher--Smith 14.2.20(1), 14.2.21--22, printed pp.988--989.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The exact marked enumeration supplies all currently established local
inputs to ambient recognition, retaining the original subgroup and involution. -/
theorem source_quintic_fusion_of_ree_tits_marks
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel :
      ChapterF.GreenBook.IsBinaryReeAmalgam
        (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
          (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right) ∨
      ChapterF.GreenBook.IsAtlasTitsAmalgam
        (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
          (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right)) :
    ChapterF.GreenBook.IsAtlasTitsAmalgam
        (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
          (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right) ∧
      H = Mc ∧ M = sourceResidual M Mc ⊔ (T : Subgroup G) ∧
      H = centralizer (centralInvolutions T : Set G) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∧
      ∃ z : G, zpowers z = centralInvolutions T ∧
        Recognition.ParrottCentralizerHypotheses z ∧ Recognition.ParrottLocalInputs z ∧
        ∃ d : Recognition.ParrottSecondElementaryData z,
          Nonempty (Recognition.ParrottNormalizerFusionData d) := by
  obtain ⟨htits,hHMc,hMX,hHC⟩ := source_tits_of_ree_tits_marks
    hG T hempty hM hu hmany hcard e H hH hmodel
  exact ⟨htits,hHMc,hMX,hHC,htits.core_quotients.1,
    source_tits_normalizer_fusion hG T hempty hM hu hmany hcard e H hH
      ⟨htits.some.left.symm⟩⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
