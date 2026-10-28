module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.ChosenClosure
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.Surviving
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.CompletedBudget

/-!
# The selected ordinary block, with the two remaining module rows exposed

Reduction (g) identifies the actual offender component as A₅. All B.5
branches except the two product-module branches now give Irr⁺ on its
literal moved subgroup. The original chosen-module classification, proved
Baumann budget and intrinsic recognition then construct all three outputs
of OrdinaryBlockSource on this very component.

The two product-module cases still require their local analysis in
qt-d-13314-ordinary-blocks; neither is an assumption of the conclusion.
The genuine earlier 13.3.2 and 12.2.13 inputs remain explicit, with final
source discharge in qt-d-1378-source.
Source: Aschbacher--Smith 13.3.14(g) and its final paragraph, p.893.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open Chapter12.Section02 Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)

/-- The full literal block-source output outside the two remaining product-module rows. -/
theorem ordinary_selected_block_or_products
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L)
    (five : PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hKs : IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
      (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hU : ⁅conjugateSpanBy U H,K.map H.subtype⁆ ≠ ⊥)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    let B := K.map H.subtype
    let J := Diagonal.localGroup B (sourceOne L T P) T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    (ChapterC.IsAlternatingBlock B 5 ∧
      (¬ sourceOne L T P ≤ B) ∧
      ⁅J.pCoreIn 2,sourceOne L T P⁆ ≤ Diagonal.movedModule B (sourceOne L T P) T) ∨
      Nonempty (SourceTwoFactorCase (ρ.comp N.subtype)) ∨
      Nonempty (HyperplaneCase (ρ.comp N.subtype)) := by
  rcases ordinary_selected_irrPlus_or_products d hmax eL escape h1332 fixed hc
      K hK hqK hf hn hgen with hi | hr
  · obtain ⟨hout,hmodel⟩ := ordinary_selected_moved_model_of_irrPlus d hmax eL escape h1332
      fixed five hc K hK hqK hf hn hgen hi
    have hcount := ordinaryChiefBudgetSource_of_original_source d hmax eL escape h1332
      K hK hKs hm hn hgen hqK hU hf hout hmodel
    obtain ⟨hbound,hlayer⟩ := ordinary_selected_block_layer_of_original_budget d eL hmax escape
      h1332 K hK hqK hf hm hn hgen hcount
    have hfaith := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mp hf
    have hblock := ordinary_alternatingBlock_of_moved_model _ _ _
      hfaith.2.1.2.1 hfaith.2.1.2.2 hlayer hmodel
    exact Or.inl ⟨hblock,hout,hbound⟩
  · exact Or.inr hr

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
