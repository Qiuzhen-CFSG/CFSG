module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.CoreReduction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection
public import Theory.GroupTheory.ReducedNormal.RepresentationEmbedding
public import Theory.GroupTheory.ReducedNormal.AmbientInclusion

/-!
# Recovering the original choice from the diagonal moved module

A.1.11 embeds the literal R₂(KT) into R₂(KL₁T). The fixed source line
supplies characteristic two for the larger local group. A chosen Irr⁺
member stays Irr⁺ under this inclusion. If the larger K-moved space is
Irr⁺, minimality identifies it with that very chosen subgroup, so the
earlier A₅ classification supplies its original conjugation marking.

The remaining B.5 row analysis must prove the explicit Irr⁺ premise;
this module does not assume a marking on the larger moved space.
The local row analysis and block assembly remain with
qt-d-13314-ordinary-blocks. The earlier fixed and A₅ classifications
remain with qt-d-1332-source; final source assembly is qt-d-1378-source.
Source: Aschbacher--Smith A.1.11, A.1.40, 13.3.2(3), and 13.3.14,
printed pp.26,31,885,892--893.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Chapter12.Section02 ChapterB.QuasisimpleSource

/-- The ambient image of the moved reduced representation is its literal group commutator. -/
theorem reduced_moved_image {G : Type*} [Group G] (J B : Subgroup G) (hBJ : B ≤ J) :
    subspaceImage J (moved (reducedRepresentation J) (B.subgroupOf J)) =
      ⁅(reducedTwoSubgroup J).map J.subtype,B⁆ := by
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have ha : reducedRepresentation J = ρ.comp q := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) g w).symm
  rw [ha,moved_comp_map]
  change subspaceImage J (subspaceCommutator ρ ⊤ ((B.subgroupOf J).map q)) = _
  rw [←NormalElementaryQuotient.commutatorSpace_eq W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) (B.subgroupOf J)]
  change ((⁅W,B.subgroupOf J⁆.subgroupOf W).map W.subtype).map J.subtype = _
  rw [map_subgroupOf_eq_of_le (commutator_le_left W _),map_commutator,
    map_subgroupOf_eq_of_le hBJ]

/-- An original chosen module exhausts an Irr⁺ moved space in a larger reduced module. -/
theorem chosen_eq_moved_of_reduced_inclusion
    {G : Type*} [Group G] {T : Sylow 2 G} {B A : Subgroup G}
    (D : ChosenModule T B A) (J : Subgroup G)
    (hJ : B ⊔ (T : Subgroup G) ≤ J)
    (hR : (reducedTwoSubgroup (B ⊔ (T : Subgroup G) : Subgroup G)).map
      (B ⊔ (T : Subgroup G) : Subgroup G).subtype ≤
        (reducedTwoSubgroup J).map J.subtype)
    (hi : IsIrrPlus (reducedRepresentation J) (B.subgroupOf J)
      (moved (reducedRepresentation J) (B.subgroupOf J))) :
    A = ⁅(reducedTwoSubgroup J).map J.subtype,B⁆ := by
  let f := ReducedNormal.moduleInclusion hJ hR
  have hI : IsIrrPlus (reducedRepresentation J) (B.subgroupOf J) (D.space.map f) :=
    ReducedNormal.isIrrPlus_ambientInclusion hJ hR le_sup_left D.irrPlus.isIrrPlus
  have hle : D.space.map f ≤ moved (reducedRepresentation J) (B.subgroupOf J) := by
    rw [←hI.choose_spec.1]
    exact subspaceCommutator_mono_left _ le_top _
  have he := IsIrrPlus.eq_of_le _ hI hi hle
  have hh := congrArg (subspaceImage J) he
  have hmap : subspaceImage J (D.space.map f) = A :=
    (ReducedNormal.subspaceImage_moduleInclusion hJ hR D.space).trans D.image_eq
  rw [hmap,reduced_moved_image J B (le_sup_left.trans hJ)] at hh
  exact hh


open Section08.SourceCompletion Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- A.1.11 on the original two local groups, with characteristic two supplied by the fixed line. -/
theorem ordinary_selected_reduced_inclusion (K : Subgroup H) :
    (reducedTwoSubgroup (K.map H.subtype ⊔ (T : Subgroup G) : Subgroup G)).map
      (K.map H.subtype ⊔ (T : Subgroup G) : Subgroup G).subtype ≤
    (reducedTwoSubgroup (Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T)).map
      (Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T).subtype := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hJH : J ≤ H := sup_le
    (sup_le (map_subtype_le _) (ordinary_point_residual_le_point d)) hTH
  have hPT : P ≤ (T : Subgroup G) :=
    d.line_le_plane.trans (d.plane_le_seed.trans (d.seed_le.trans d.chosen.le_sylow))
  have hP : P ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hPT) (hPT.trans le_sup_right)
    (hJH.trans d.first_normalizer.le)
  have hPn : P ≠ ⊥ := by intro he; have hh := d.line_card; simp [he] at hh
  have hchar : J ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (d.counterexample.qtke.evenCharacteristic T)
      ⟨(fun he => hPn (bot_unique (he ▸ hP))),fun _ ht =>
        (show (T : Subgroup G) ≤ J from le_sup_right) ht⟩
  exact reducedPSubgroup_ambient_le T (B ⊔ (T : Subgroup G)) J le_sup_right
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right) (Chapter1.mem_He_iff.mp hchar)

/-- Irr⁺ of the literal moved space recovers an original choice in R₂(KT). -/
theorem ordinary_selected_chosen_of_moved_irrPlus
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hi : let J := Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T
      IsIrrPlus (reducedRepresentation J) ((K.map H.subtype).subgroupOf J)
        (moved (reducedRepresentation J) ((K.map H.subtype).subgroupOf J))) :
    Nonempty (ChosenModule T (K.map H.subtype)
      (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T)) := by
  have hh := ordinary_selected_hypothesis1223 d h1332 K hqK hf
  obtain ⟨A,⟨D⟩⟩ := hh.toHypothesis1221.exists_chosen_of_normalizes (h1332 _ hf).1
  have he := chosen_eq_moved_of_reduced_inclusion D
    (Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T)
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    (ordinary_selected_reduced_inclusion d K) hi
  change A = Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T at he
  exact he ▸ ⟨D⟩

/-- The remaining Irr⁺ assertion gives the actual A₅ marking, using only the earlier module catalogue. -/
theorem ordinary_selected_moved_model_of_irrPlus
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : FixedModule1332At T L)
    (five : PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K)
    (hi : let J := Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T
      IsIrrPlus (reducedRepresentation J) ((K.map H.subtype).subgroupOf J)
        (moved (reducedRepresentation J) ((K.map H.subtype).subgroupOf J))) :
    (¬ sourceOne L T P ≤ K.map H.subtype) ∧
      Chapter6.Source.IsConjugationModel (K.map H.subtype)
        (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T)
        Chapter6.Source.a5Module := by
  obtain ⟨hout,hfive⟩ := ordinary_selected_five_quotient_of_fixed_module_source d hmax eL escape
    h1332 fixed hc K hK hqK hf hn hgen
  obtain ⟨D⟩ := ordinary_selected_chosen_of_moved_irrPlus d h1332 K hqK hf hi
  exact ⟨hout,five G T L d.counterexample _ hf hfive _ D⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
