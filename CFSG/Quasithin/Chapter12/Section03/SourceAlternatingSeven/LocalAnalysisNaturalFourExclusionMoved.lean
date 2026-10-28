module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionEnlargements
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NonsplitMoved

/-!
# A nonsplit natural moved section for the actual central-line enlargement

The strict overcomponent supplied by the source block argument has a genuine
C.2.7 input. Its moved star module is V(K,O₂(KT)), so it contains the
original V and the fixed involution z. Applying the fixed-point obstruction
to the proved B.5.1 conclusion excludes splitting and gives Irr⁺ and the
nonsplit natural action list on the literal quotient of this moved section.
The original O₂(N_K(V)) still centralizes V.

This is the module-selection input to the remaining enlargement exclusion;
it does not select the A₈ row or assert the final transvection contradiction.
Source: Aschbacher–Smith, Lemma 12.3.3, printed pp.807–808, using B.5.1(2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

/-- The central-line residual produces an actual nonsplit natural section,
with the original embedding of V and the normalizer-core obstruction. -/
theorem four_exists_nonsplit_enlargement
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    let Q := S.fourComponentPointCore z
    ∃ K : Subgroup G,
      S.fourComponentPointPerfect z < K ∧
      Input KnownSimple.IsKnownSimple (S.fourPointCentralizer z) Q (S.fourPointLocal z) K ∧
      KernelConclusion K Q ∧ OffenderConclusion K Q ∧
      (K ⊓ normalizer (V : Set G)).pCoreIn 2 ≤ centralizer (V : Set G) ∧
      V ≤ (⁅starV K Q,K.subgroupOf (K ⊔ Q)⁆).map (K ⊔ Q).subtype ∧
      z ∈ (⁅starV K Q,K.subgroupOf (K ⊔ Q)⁆).map (K ⊔ Q).subtype ⊓
        centralizer (K : Set G) ∧
      (let ρ := starRepresentation K Q
       let J := offenderSubgroup ρ
       starImage K Q K ≤ J ∧
         Nonempty (ChapterC.C27Source.NonsplitMovedConclusion (ρ.comp J.subtype)
           ((starImage K Q K).subgroupOf J))) := by
  obtain ⟨K,hDK,hi,hn,hker,hoff,hcent,hcores,hV,hzK⟩ :=
    S.four_exists_quasisimple_C27_enlargement structural escape e hd hz hz1 hzT
  have he := S.four_overcomponent_star_moved_eq structural e hd hz hz1 hzT hi.component hDK.le
  have hzstar : z ∈ (⁅starV K (S.fourComponentPointCore z),
      K.subgroupOf (K ⊔ S.fourComponentPointCore z)⁆).map
        (K ⊔ S.fourComponentPointCore z).subtype ⊓ centralizer (K : Set G) := by
    rwa [he]
  refine ⟨K,hDK,hi,hker,hoff,hcent,?_,hzstar,
    ChapterC.C27Source.star_moved_nonsplit_of_fixed_point hi hz1 hzstar⟩
  rwa [he]

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
