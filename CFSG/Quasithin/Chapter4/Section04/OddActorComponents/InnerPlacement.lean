module
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Models
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.PerfectActors

/-!
# Inner placement for the actual selected odd-normalizer component

The genuine earlier A/B theorems select K and its full central-quotient model.
The explicit full-B outer input then makes the original perfect L_A action
inner. The result retains the actual N(A) carrier and both normalizations;
no SQTK hypothesis on N(A), center-free cover, or invariant V under N(L)
is used. Full B-only outer solvability is the remaining model obligation.
Source: Aschbacher–Smith 4.4.3, printed p.621.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

theorem chosen_oddNormalizer_exists_inner_component
    {κ : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}
    (hA : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremA κ X)
    (hB : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremB κ X)
    (hOuter : ChapterA.Section03.SourceComponents.TheoremBOuter.SourceInput.{u})
    (h : Chapter12.Section02.Hypothesis1221 κ T L)
    (D : Chapter12.Section02.ChosenModule T L V) (hcard : Nat.card V = 64)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hodd : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (hunique : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        K ⊔ centralizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) := by
  obtain ⟨K,hK,hm,houtK,hcore,hmodel,hFK,hVK⟩ :=
    chosen_oddNormalizer_exists_theoremB_component hA hB h D hcard A hne hAN hcomm hodd hAV hunique hout
  let : IsQuasisimple K := hK.2
  let F := oddActorResidual L A
  let N := normalizer (A : Set G)
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hFN).symm.surjective
  exact ⟨K,hK,hm,houtK,hcore,hmodel,
    ChapterA.Section03.SourceComponents.TheoremBOuter.perfect_actor_inner
      hOuter K (F.subgroupOf N) hmodel hFK,hVK⟩
end CFSG.Quasithin.Chapter4.Section04
