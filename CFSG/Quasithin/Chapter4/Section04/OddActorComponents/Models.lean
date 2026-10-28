module
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Action
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleModels
/-!
# The full source model of the detected odd-normalizer component

The genuine universal A/B inputs classify the literal simple central quotient
of the component selected outside N(L). The conclusion retains its original
inclusion in N(A), full chosen-module commutator, and residual normalizer.
No truncated catalogue or quasithin quotient hypothesis is substituted.

Source: Aschbacher--Smith, paragraph preceding 4.4.10, printed p.621.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
universe u
variable {G:Type u} [Group G] [Finite G]
/-- The actual selected component carries the complete earlier B-model predicate. -/
theorem chosen_oddNormalizer_exists_theoremB_component
    {κ:GroupClass.{u}} {T:Sylow 2 G} {L V:Subgroup G}
    (hA:∀(X:Type u)[Group X][Finite X],ChapterA.Section02.TheoremA κ X)
    (hB:∀(X:Type u)[Group X][Finite X],ChapterA.Section02.TheoremB κ X)
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V) (hcard:Nat.card V=64)
    (A:Subgroup G) [IsMulCommutative A] (hne:A≠⊥)
    (hAN:A≤normalizer (L:Set G)) (hcomm:⁅A,L⁆≤L.pCoreIn 2)
    (hodd:Odd (Nat.card A)) (hAV:A≤centralizer (V:Set G))
    (hunique:UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L:Set G)))
    (hout:¬normalizer (A:Set G)≤normalizer (L:Set G)) :
    ∃K:Subgroup (normalizer (A:Set G)),
      IsComponent (normalizer (A:Set G)) K ∧
      ⁅K,V.subgroupOf (normalizer (A:Set G))⁆=K ∧
      ¬K.map (normalizer (A:Set G)).subtype≤normalizer (L:Set G) ∧
      pCore 2 K=⊥ ∧ ChapterA.Section02.IsTheoremBModel (K⧸center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A:Set G))≤
        normalizer (K:Set (normalizer (A:Set G))) ∧
      V.subgroupOf (normalizer (A:Set G))≤normalizer (K:Set (normalizer (A:Set G))) := by
  obtain ⟨K,hK,hm,houtK,hcore,hqt,_,hFK,hVK⟩:=
    chosen_oddNormalizer_exists_full_component_action h D hcard A hne hAN hcomm hodd hAV hunique hout
  let : IsQuasisimple K:=hK.2
  have hproper:normalizer (A:Set G)≠⊤:=(oddNormalizer_properQTK h.simpleQTKE A hne).1
  have hκ:IsKGroup κ K:=(h.simpleQTKE.properK _ hproper).subgroup K
  exact ⟨K,hK,hm,houtK,hcore,
    ChapterA.Section02.quasisimple_centralQuotient_theoremBModel (hA K) (hB _) hqt hκ,hFK,hVK⟩
end CFSG.Quasithin.Chapter4.Section04
