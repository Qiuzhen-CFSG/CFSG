module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.Products
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.Selected

/-!
# Completed ordinary A₅ block geometry

The product rows complete the moved-module sieve on the literal offender
component. Recovering the original chosen module supplies the A₅ action;
the proved diagonal Baumann identity and chief budget then recognize the
block and bound the original two-core commutator. The actual plane and
Section 13.8 source consumers are included, without assuming that the full
V-span is nonabelian or using later plane noncentrality.

Only genuine earlier 13.3.2 and 12.2.13 inputs remain explicit. Their
producers are qt-d-1332-source and qt-d-1222-recognition, and their final
source discharge belongs to qt-d-1378-source.
Source: Aschbacher--Smith 13.3.14(g) and final paragraph, pp.892--893.
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
include d

/-- Every surviving source row gives Irr⁺ on the literal diagonal moved space. -/
theorem ordinary_selected_moved_irrPlus
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L) (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K) :
    let B := K.map H.subtype
    let J := Diagonal.localGroup B (sourceOne L T P) T
    IsIrrPlus (reducedRepresentation J) (B.subgroupOf J)
      (moved (reducedRepresentation J) (B.subgroupOf J)) := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BJ := B.subgroupOf J
  let Bq := BJ.map q
  obtain ⟨hBq,hcomp,hrows⟩ :=
    ordinary_selected_offender_entry_of_original_source d hmax eL escape h1332 K hK hqK hf
  obtain ⟨e⟩ := ordinary_selected_offender_component_five d hmax eL escape h1332 fixed hc
    K hK hqK hf hn hgen
  have hcard : Nat.card (Bq.subgroupOf N) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hi : IsIrrPlus (ρ.comp N.subtype) (Bq.subgroupOf N)
      (moved (ρ.comp N.subtype) (Bq.subgroupOf N)) := by
    rcases component_card_sixty_irrPlus_or_products (ρ.comp N.subtype) (Bq.subgroupOf N)
        hcomp hcard hrows with hi | hr
    · exact hi
    · rcases hr with hc | hc
      · obtain ⟨c⟩ := hc
        exact twoFactor_moved_irrPlus_of_component_five _ _ hcomp e c
      · obtain ⟨c⟩ := hc
        exact hyperplane_moved_irrPlus_of_component_five _ _ hcomp e c
  have hspace : moved (ρ.comp N.subtype) (Bq.subgroupOf N) = moved ρ Bq := by
    rw [moved_comp_map,map_subgroupOf_eq_of_le hBq]
  rw [hspace] at hi
  have hi' : IsIrrPlus ρ Bq (moved ρ Bq) :=
    (IsIrrPlus.subgroupOf_iff ρ Bq N hBq _).mp hi
  have ha : reducedRepresentation J = ρ.comp q := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) g w).symm
  have hi'' := IsIrrPlus.map_embedding (reducedRepresentation J) ρ q
    (LinearMap.id : Additive W →ₗ[ZMod 2] Additive W)
    Function.injective_id (fun g w => by rw [ha]; rfl) BJ (moved ρ Bq) hi'
  change IsIrrPlus (reducedRepresentation J) BJ (moved (reducedRepresentation J) BJ)
  simpa only [Submodule.map_id,ha,moved_comp_map] using hi''



/-- The complete ordinary moved-module source, retaining only earlier source inputs. -/
theorem ordinaryMovedModuleSource_of_original_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L)
    (five : PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥) : OrdinaryMovedModuleSource d := by
  intro K hK _ _ hn hgen hq _ hf
  exact ordinary_selected_moved_model_of_irrPlus d hmax eL escape h1332 fixed five hc
    K hK hq hf hn hgen
    (ordinary_selected_moved_irrPlus d hmax eL escape h1332 fixed hc K hK hq hf hn hgen)

/-- All three selected-component block conclusions under the original contrary assumption. -/
theorem ordinaryBlockSource_of_original_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L)
    (five : PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥) : OrdinaryBlockSource d :=
  ordinaryBlockSource_of_module_and_chief_sources d hmax eL h1332 escape
    (ordinaryMovedModuleSource_of_original_source d hmax eL escape h1332 fixed five hc)
    (ordinaryChiefBudgetSource_of_original_source d hmax eL escape h1332)

/-- The original ordinary A₆ plane noncentrality, with the local block chain discharged. -/
theorem ordinary_plane_noncentral_of_original_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L)
    (five : PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    ⁅H.pCoreIn 2,E⁆ ≠ ⊥ :=
  Chapter14.Section08.LieTypeBranch.original_six_plane_noncentral_of_diagonal_source
    d hmax eL h1332 escape (fun hc => ordinaryDiagonalSource_of_blocks d h1332
      (ordinaryBlockSource_of_original_source d hmax eL escape h1332 fixed five hc))

/-- The actual Section 13.8 source input, now with all ordinary block premises supplied. -/
theorem ordinary_selected_source_inputs_of_original_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L)
    (five : PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    H ∈ Chapter13.Section08.Source.Hz (sourceOne L T P) T H M ∧
      IsMulCommutative (conjugateSpanBy V H) ∧
      ∀ A ∈ Chapter13.Section08.Source.Hz (sourceOne L T P) T H M,
        (Chapter13.Section07.ConjugateIntersections.sourceSetup T L V U P A).Hypothesis ∧
        IsMulCommutative (Chapter13.Section08.Source.VH A V) ∧
        ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) A V,
          Odd c.path.length ∧
          Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c U P ∧
          ¬ ⁅c.Ugamma U,V⁆ ≤ c.Aone P :=
  Chapter14.Section08.LieTypeBranch.original_six_selected_source_inputs_of_blocks
    d hmax eL h1332 five escape
    (ordinaryBlockSource_of_original_source d hmax eL escape h1332 fixed five)

omit d in
/-- Original chosen-module selection followed by the completed ordinary source application. -/
theorem exists_ordinary_selected_source_inputs_of_original_source
    (hmax : Maximal (Counterexample T) L)
    (natural : ∃ V : Subgroup G, Nonempty (ChosenModule T L V) ∧
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      Chapter6.Source.IsConjugationModel L V
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L)
    (five : PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    ∃ V P E U : Subgroup G,
      Nonempty (NaturalSetup T L V P E U (normalizer (L : Set G)) (normalizer (P : Set G))) ∧
      normalizer (P : Set G) ∈ Chapter13.Section08.Source.Hz (sourceOne L T P) T
        (normalizer (P : Set G)) (normalizer (L : Set G)) ∧
      IsMulCommutative (conjugateSpanBy V (normalizer (P : Set G))) ∧
      ∀ A ∈ Chapter13.Section08.Source.Hz (sourceOne L T P) T
          (normalizer (P : Set G)) (normalizer (L : Set G)),
        (Chapter13.Section07.ConjugateIntersections.sourceSetup T L V U P A).Hypothesis ∧
        IsMulCommutative (Chapter13.Section08.Source.VH A V) ∧
        ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) A V,
          Odd c.path.length ∧
          Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c U P ∧
          ¬ ⁅c.Ugamma U,V⁆ ≤ c.Aone P := by
  obtain ⟨V,⟨D⟩,hTV,hmodel⟩ := natural
  obtain ⟨P,E,U,⟨d⟩⟩ := Chapter14.Section08.LieTypeBranch.exists_original_six_setup_of_chosen_module hmax.1 D hTV hmodel
  obtain ⟨eL,_,_⟩ := hmodel
  exact ⟨V,P,E,U,⟨d⟩,ordinary_selected_source_inputs_of_original_source d hmax eL
    escape h1332 fixed five⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
