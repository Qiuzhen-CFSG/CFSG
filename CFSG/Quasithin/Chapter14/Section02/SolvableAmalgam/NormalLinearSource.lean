module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalLinearBound
public import CFSG.Quasithin.Chapter14.Section02.KOneSource
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Applying the normal linear bound to the original selected component

The original H* minimal-parabolic theorem identifies H∩M with the unique
maximal overgroup of the prescribed Sylow subgroup. The proved normal
linear/Suzuki cover theorem then identifies its core with O₂(H). Applying
the Frattini orbit bound leaves only field degrees two and three.

This is the literal selected-component consumer of the numerical step in
Aschbacher–Smith 14.2.16, printed pp.985–986.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- In the actual selected normal linear branch, the core equality follows
from the original minimal-parabolic theorem, so no action or core premise remains. -/
theorem source_normal_linear_degree
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
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hm : ModelBorelPair ((H ⊓ M).subgroupOf H) K (BenderSuzuki.Converse.PBorel F)) :
    n = 2 ∨ n = 3 := by
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
  have hmodel : ExchangedModel (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) K n := by
    rw [←hmax]
    exact .inl ⟨F,inferInstance,inferInstance,inferInstance,hn,hF,hm⟩
  obtain ⟨_,hcore,_,_,_⟩ := source_normal_rank_one_kOne _ hP hs K hK hqK hgen hmodel
  have hc : sourceKernel ((H ⊓ M).subgroupOf H) = pCore 2 H := by
    rw [hmax]
    exact hcore
  exact source_nonabelian_linear_degree hG T hempty hM hu hmany hcard e H hH.1 hne
    K hgen hc n hn hF hm
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
