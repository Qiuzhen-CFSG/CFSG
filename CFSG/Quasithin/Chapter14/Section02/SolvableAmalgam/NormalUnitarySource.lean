module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalUnitaryExclusion
public import CFSG.Quasithin.Chapter14.Section02.KOneSource
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalRank
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original normal unitary source exclusion

The H* theorem identifies the literal overlap H∩M with the unique maximal
subgroup of the chosen minimal parabolic. Its normal-core quotient acts
faithfully on the marked PSU₃ factor. The original central-kernel theorem
preserves two-rank on passing from H/O₂(H) to that quotient, retaining the
possible odd scalar center of SU₃.

The nonabelian Frattini orbit obstruction now excludes the entire normal
unitary row without a rank, core-equality, automorphism, or orbit premise.
Source: the normal Bender branch leading to Aschbacher–Smith 14.2.16,
printed pp.985–986.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The selected normal unitary row is impossible when the original closure is nonabelian. -/
theorem source_normal_unitary_false
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
    {n : ℕ} (hm : UnitaryModel ((H ⊓ M).subgroupOf H) K n) : False := by
  obtain ⟨_,hP,hN,_,_,_⟩ :=
    source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
  have hSN : (T.subtype hH.1.1.2 : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
    intro x hx
    exact ⟨x.property,hM.1.2 hx⟩
  have hmax : (H ⊓ M).subgroupOf H =
      ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP :=
    ChapterB.minimalParabolicMax_unique _ hP hN hSN
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hnH) generationParameter_le_one_of_solvable
  obtain ⟨F,hfield,hfinite,hchar,J,hJ,hn,hF,hconj,hfixed,hm⟩ := hm
  have hstar := hm.unitary_source_actor_two_rank (T.subtype hH.1.1.2)
    _ K hgen hSN J hJ hn hF hconj hfixed
  have hr : primeRank 2 (H ⧸ pCore 2 H) ≤ n+1 := by
    rw [source_single_two_rank_eq (T.subtype hH.1.1.2) hP hs K hK hqK hgen]
    have transport (N N' : Subgroup H) (he : N = N') :
        primeRank 2 (H ⧸ sourceKernel N) ≤ n+1 →
        primeRank 2 (H ⧸ sourceKernel N') ≤ n+1 := by
      subst N'
      exact id
    exact transport _ _ hmax hstar
  exact source_nonabelian_unitary_false_of_rank hG T hempty hM hu hmany hcard e H hH.1
    hne K hgen J hJ n hn hF hfixed hm hr
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
