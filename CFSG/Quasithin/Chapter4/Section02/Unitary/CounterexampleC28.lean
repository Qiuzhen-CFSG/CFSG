module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.SourceSetup
import Mathlib.Tactic
/-!
# From the original odd actor to the genuine C.2.8 configuration

Failure of maximal-two-local uniqueness selects a maximal source
counterexample. Its two-core lies in an actual Sylow section centralizer;
the preceding source setup applies, and Sylow conjugacy records the embedding
of the original chosen module into the resulting full module. The final
specialization uses precisely the perfect residual from 4.4.5.

Source: Aschbacher–Smith, 4.2.12–13 and 4.4.5–6, printed pp.610–612,620.
-/
public section
namespace CFSG.Quasithin.Chapter4.Section02.Unitary
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- An actual covering subgroup whose uniqueness fails supplies the full
C.2.8 configuration and a marked copy of the original chosen module. -/
theorem exists_source_C28_of_not_unique {K : GroupClass} {T : Sylow 2 G}
    {L V I : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 K T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hIN : I ≤ normalizer (L : Set G))
    (hcover : (L : Set G) ⊆ (I : Set G) * (L.pCoreIn 2 : Set G))
    (hcore : I.pCoreIn 2 ≠ ⊥)
    (hnot : ¬ UniqueMaximalOvergroup I (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)),
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L I) ∧
      PushLE L I J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ H ⊓ normalizer (L : Set G) < H ∧
      J.pCoreIn 2 ≤ (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      ChapterC.HypothesisC28 K H (H ⊓ normalizer (L : Set G))
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) (J.pCoreIn 2)
        (fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        V.map (MulAut.conj (c : G)).toMonoidHom ≤
          fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) := by
  obtain ⟨hs,_⟩ := coveringOvergroup_eta L.le_normalizer le_rfl hIN hcover hcore
  obtain ⟨J,H,hJ,hIJ,hH,hJH,hout,_⟩ := maximal_counterexample_of_component_cover
    h.simpleQTKE hM.1 L.le_normalizer le_rfl hIN hcover hcore hnot
  have hyp := source_hypothesis411 h hM
  have hJC := core_le_sectionCentralizer_of_eta hyp.plus_le hyp.plus_normal
    hyp.plus_perfect hs.1 hJ.1.1
  let C := sectionCentralizerIn (normalizer (L : Set G)) L
  obtain ⟨S,hRS⟩ := ((isPGroup_pCoreIn 2 J).comap_subtype :
    IsPGroup 2 ((J.pCoreIn 2).subgroupOf C)).exists_le_sylow
  have hRS' : J.pCoreIn 2 ≤ (S : Subgroup C).map C.subtype := by
    intro x hx
    exact ⟨⟨x,hJC hx⟩,hRS hx,rfl⟩
  have hlt : H ⊓ normalizer (L : Set G) < H :=
    lt_of_le_not_ge inf_le_left (fun he => hout (he.trans inf_le_right))
  exact ⟨J,H,S,hJ,hIJ,hH,hJH,hout,hlt,hRS',
    source_C28_of_muStar h D hM hs hJ hH hJH hout S hRS',
    exists_fullModule_comparison h D hM S⟩

/-- Literal 4.4.5 consumer: the original odd actor and chosen module
construct C.2.8 whenever the actual perfect residual fails uniqueness. -/
theorem chosen_oddActorResidual_C28 {K : GroupClass} {T : Sylow 2 G}
    {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 K T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (B : Subgroup G) (hBN : B ≤ normalizer (L : Set G))
    (hcomm : ⁅B,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card B))
    (hBV : B ≤ centralizer (V : Set G))
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hnot : ¬ UniqueMaximalOvergroup (Section04.oddActorResidual L B)
      (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)),
      PushLE L (Section04.oddActorResidual L B) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      ChapterC.HypothesisC28 K H (H ⊓ normalizer (L : Set G))
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) (J.pCoreIn 2)
        (fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        V.map (MulAut.conj (c : G)).toMonoidHom ≤
          fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) := by
  obtain ⟨hc,_,_,hne⟩ := Section04.chosen_oddActorResidual_cover h D B hBN hcomm hodd hBV
  have hi := ((Section04.oddActorResidual_le L B).trans inf_le_left).trans L.le_normalizer
  obtain ⟨J,H,S,_,hIJ,hH,hJH,_,hlt,_,hs,hmark⟩ :=
    exists_source_C28_of_not_unique h D hM hi hc.subset hne hnot
  exact ⟨J,H,S,hIJ,hH,hJH,hlt,hs,hmark⟩
end CFSG.Quasithin.Chapter4.Section02.Unitary
