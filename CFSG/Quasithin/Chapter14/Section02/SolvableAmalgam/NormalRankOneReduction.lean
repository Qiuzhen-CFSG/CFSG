module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalLinearSource
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalSuzukiExclusion
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original normal rank-one alternative

For the selected subgroup in §14.2, a nonabelian conjugate closure forces the
normal rank-one component to be linear over the fields of order four or eight.
The original minimal-parabolic hypotheses identify the marked Borel kernel with
the two-core; the Frattini orbit bounds then exclude Suzuki and bound the linear
field. This supplies the numerical normal branch used before source 14.2.16.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The genuine original normal linear/Suzuki alternative reduces to the
marked linear fields four or eight whenever the source closure is nonabelian. -/
theorem source_normal_rank_one_nonabelian_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (f : ℕ) (hm : ExchangedModel ((H ⊓ M).subgroupOf H) K f) :
    (f = 2 ∨ f = 3) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 2^f ∧
        ModelBorelPair ((H ⊓ M).subgroupOf H) K (BenderSuzuki.Converse.PBorel F) := by
  rcases hm with ⟨F,hF,hfin,hchar,hf,hcardF,hmark⟩ | ⟨m,hmpos,hfm,hmark⟩
  · exact ⟨source_normal_linear_degree hG T hempty hM hu hmany hcard e H hH hnH hne
      K hK hqK hgen f hf hcardF hmark,F,hF,hfin,hchar,hcardF,hmark⟩
  · exfalso
    obtain ⟨_,hP,hN,_,_,_⟩ :=
      source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
    have hmax : (H ⊓ M).subgroupOf H = ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP :=
      ChapterB.minimalParabolicMax_unique _ hP hN (by
        intro x hx
        exact ⟨x.property,hM.1.2 hx⟩)
    have hs : ¬Group.IsSolvable H := by
      intro hs
      let := hs
      exact (Nat.not_le_of_gt hnH) generationParameter_le_one_of_solvable
    have hmodel : ExchangedModel (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) K f := by
      rw [←hmax]
      exact .inr ⟨m,hmpos,hfm,hmark⟩
    obtain ⟨_,hcore,_,_,_⟩ := source_normal_rank_one_kOne _ hP hs K hK hqK hgen hmodel
    have hc : sourceKernel ((H ⊓ M).subgroupOf H) = pCore 2 H := by
      rw [hmax]
      exact hcore
    exact source_nonabelian_suzuki_false hG T hempty hM hu hmany hcard e H hH.1 hne
      K hgen hc m hmpos hmark
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
