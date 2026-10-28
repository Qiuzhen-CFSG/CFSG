module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBlockModulesAt
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryPlaneSourceAt
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.Complete

/-!
# Complete ordinary block and selected-source assembly with local inputs

The completed product-row calculations give Irr⁺ on the same moved module.
Its original local A₅ marking, diagonal Baumann identity and chief budget
construct every OrdinaryBlockSource output. The plane contradiction and full
ordinary chain then supply G₁ in Hz, the abelian full span, F.9 and the selected
critical geometry, also starting from one existential natural chosen module.

This consumes the completed block geometry of qt-d-13314-ordinary-blocks.
Only the original fixed/A₅ module clauses, Source1332OneTwo, natural choice
and local recognition remain. Their genuine earlier producers are
qt-d-1332-source and qt-d-1222-source; final source discharge stays with
qt-d-1378-source and qt-d-1381-source.
Source: Aschbacher–Smith 13.3.14,13.7.8,13.8.2–8, pp.891–893,940–949.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterB.SourceInduction ChapterB.QuasisimpleSource Chapter12.Section02
open Representation.BinaryOffender.Homogeneous
open Section08.SourceCompletion Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

theorem ordinary_selected_moved_irrPlus_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : Chapter13.Section03.SourceCompletion.OriginalFixedModule1332At T L) (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
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
    ordinary_selected_offender_entry_of_original_source_at d hmax eL escape h1332 K hK hqK hf
  obtain ⟨e⟩ := ordinary_selected_offender_component_five_at d hmax eL escape h1332 fixed hc
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

theorem ordinaryMovedModuleSource_of_original_source_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : Chapter13.Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥) : OrdinaryMovedModuleSource d := by
  intro K hK _ _ hn hgen hq _ hf
  exact ordinary_selected_moved_model_of_irrPlus_at d hmax eL escape h1332 fixed five hc
    K hK hq hf hn hgen
    (ordinary_selected_moved_irrPlus_at d hmax eL escape h1332 fixed hc K hK hq hf hn hgen)

theorem ordinaryBlockSource_of_original_source_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : Chapter13.Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥) : OrdinaryBlockSource d :=
  ordinaryBlockSource_of_module_and_chief_sources_at d hmax eL h1332 escape
    (ordinaryMovedModuleSource_of_original_source_at d hmax eL escape h1332 fixed five hc)
    (ordinaryChiefBudgetSource_of_original_source_at d hmax eL escape h1332)

theorem ordinary_plane_noncentral_of_original_source_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : Chapter13.Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L) :
    ⁅H.pCoreIn 2,E⁆ ≠ ⊥ :=
  Chapter14.Section08.LieTypeBranch.original_six_plane_noncentral_of_diagonal_source_at
    d hmax eL h1332 escape (fun hc => ordinaryDiagonalSource_of_blocks d h1332
      (ordinaryBlockSource_of_original_source_at d hmax eL escape h1332 fixed five hc))

theorem ordinary_selected_source_inputs_of_original_source_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : Chapter13.Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L) :
    H ∈ Chapter13.Section08.Source.Hz (sourceOne L T P) T H M ∧
      IsMulCommutative (conjugateSpanBy V H) ∧
      ∀ A ∈ Chapter13.Section08.Source.Hz (sourceOne L T P) T H M,
        (Chapter13.Section07.ConjugateIntersections.sourceSetup T L V U P A).Hypothesis ∧
        IsMulCommutative (Chapter13.Section08.Source.VH A V) ∧
        ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) A V,
          Odd c.path.length ∧
          Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c U P ∧
          ¬ ⁅c.Ugamma U,V⁆ ≤ c.Aone P :=
  Chapter14.Section08.LieTypeBranch.original_six_selected_source_inputs_of_blocks_at
    d hmax eL h1332 five escape
    (ordinaryBlockSource_of_original_source_at d hmax eL escape h1332 fixed five)

omit d in
theorem exists_ordinary_selected_source_inputs_of_original_source_at
    (hmax : Maximal (Counterexample T) L)
    (natural : ∃ V : Subgroup G, Nonempty (ChosenModule T L V) ∧
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      Chapter6.Source.IsConjugationModel L V
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : Chapter13.Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L) :
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
  exact ⟨V,P,E,U,⟨d⟩,ordinary_selected_source_inputs_of_original_source_at d hmax eL
    escape h1332 fixed five⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
