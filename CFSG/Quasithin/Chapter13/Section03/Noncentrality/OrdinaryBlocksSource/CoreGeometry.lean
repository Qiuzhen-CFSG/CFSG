module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.Escape
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryChiefControl
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs
public import Theory.ThreeSubgroups
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryDiagonalModels
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryLinearThreeExclusion

/-!
# The intrinsic component layer after the ordinary chief-factor bound

The faithful reduced action makes the actual W_K nontrivial. Hence the
original two-chief-factor estimate applies without a separate nonzero-module
premise. Once [O₂(J),L₁] lies in W_K, the relative three-subgroups lemma and
[K,L₁]=K put [O₂(J),K] there as well. Coprime commutator idempotence identifies
W_K with the embedded intrinsic block layer [O₂(K),K].

The final application uses the selected K in the original point normalizer,
with all core and residual maps unchanged. Its chief budget remains the
source obligation coming from Baumann escape and 13.3.10; no block structure
or model marking is assumed in this group-theoretic step.

Source: Aschbacher--Smith, 13.3.14, final paragraph, printed p.893.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Generation by the actor turns its core bound into the intrinsic block-layer equality. -/
theorem ordinary_blockU_eq_moved_of_core_bound
    (K A T : Subgroup G) (hp : IsPPerfect 2 K)
    (hn : A ≤ normalizer (K : Set G)) (hTK : T ≤ normalizer (K : Set G))
    (hgen : ⁅K,A⁆ = K)
    (hbound : ⁅(Diagonal.localGroup K A T).pCoreIn 2,A⁆ ≤
      Diagonal.movedModule K A T) :
    (ChapterC.blockU K).map K.subtype = Diagonal.movedModule K A T := by
  let J := Diagonal.localGroup K A T
  let R := Diagonal.reducedModule K A T
  let W := Diagonal.movedModule K A T
  let Q := J.pCoreIn 2
  have hKJ : K ≤ J := le_sup_left.trans le_sup_left
  have hAJ : A ≤ J := le_sup_right.trans le_sup_left
  have hJK : J ≤ normalizer (K : Set G) := sup_le (sup_le K.le_normalizer hn) hTK
  have hJW : J ≤ normalizer (W : Set G) :=
    reduced_image_commutator_normalized J K hKJ hJK
  have hJQ : J ≤ normalizer (Q : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hKQ : K ≤ normalizer (Q : Set G) := hKJ.trans hJQ
  have hQJ : Q ≤ J := pCoreIn_le 2 J
  have hQK : ⁅Q,K⁆ ≤ W := by
    have h1 : ⁅⁅A,Q⁆,K⁆ ≤ W := by
      rw [commutator_comm A Q]
      exact (commutator_mono hbound le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hKJ.trans hJW))
    have h2 : ⁅⁅Q,K⁆,A⁆ ≤ W :=
      (commutator_mono (le_normalizer_iff_commutator_le_left.mp hKQ) le_rfl).trans hbound
    have hh := commutator_commutator_le_of_rotate_of_le_normalizer
      (hKJ.trans hJW) (hAJ.trans hJW) (hQJ.trans hJW) h1 h2
    rwa [hgen,commutator_comm K Q] at hh
  have hRQ : R ≤ Q := map_mono (reducedPSubgroup_le_pCore 2 J)
  have hRW : W ≤ R := reduced_image_commutator_le J K hKJ
  have hWB : W ≤ K :=
    le_normalizer_iff_commutator_le_right.mp ((hRQ.trans hQJ).trans hJK)
  have hWK : W ≤ K.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 J).to_le (hRW.trans hRQ)) hWB
      (hKJ.trans hJW)
  have hRN : K ≤ normalizer (R : Set G) := by
    have hh := (reducedTwoSubgroup J).le_normalizer_map J.subtype
    rw [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hKJ.trans hh
  have hid : ⁅W,K⁆ = W :=
    commutator_isPPerfect_idempotent K R hp ((isPGroup_pCoreIn 2 J).to_le hRQ) hRN
  change (⁅pCore 2 K,(⊤ : Subgroup K)⁆).map K.subtype = W
  rw [map_commutator,← MonoidHom.range_eq_map,range_subtype]
  apply le_antisymm
  · exact (commutator_mono (pCoreIn_mono_of_normalizes hKJ hJK) le_rfl).trans hQK
  · exact hid.symm.le.trans (commutator_mono hWK le_rfl)

variable {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- Reduction (g) leaves exactly the A₅ quotient on the ambient selected component.
The linear-three projection is forced back into K by its Sylow invariance. -/
theorem ordinary_selected_five_quotient_of_noncontainment
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K)
    (hnot : ¬sourceOne L T P ≤ K.map H.subtype) :
    Nonempty ((K.map H.subtype ⧸ pCore 2 (K.map H.subtype)) ≃*
      alternatingGroup (Fin 5)) := by
  rcases ordinary_selected_small_quotient d eL h1332 K hK hqK hf hnot with
    hfive | ⟨F,_,_,hc,⟨e⟩⟩
  · exact hfive
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hc)
  have hnG : sourceOne L T P ≤ normalizer (K.map H.subtype : Set G) := by
    have hh := (map_mono hn).trans (K.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hh
  have hgenG := congrArg (map H.subtype) hgen
  rw [map_commutator,map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hgenG
  exact (hnot (Diagonal.actor_le_of_linearThree_quotient _ _ T hnG
    (T_normalizes_one L T P d.line_stable) (h1332 _ hf).1
    ordinary_point_residual_twoPerfect (ordinary_point_residual_quotient_card d eL)
    hgenG (e.trans (Atlas.fieldEquivPSL 3 eF)))).elim

/-- The source offender entry ensures that the original moved module survives. -/
theorem ordinary_selected_moved_ne_bot_of_escape
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hescape : ¬ H ≤ M)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T ≠ ⊥ := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  let W := reducedTwoSubgroup J
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  obtain ⟨hle,hcomp,_⟩ :=
    ordinary_selected_offender_entry_of_escape d h1221 hescape h1332 K hK hqK hf
  intro hz
  have hcomm : ⁅W,B.subgroupOf J⁆ = ⊥ := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hBJ,Subgroup.map_bot]
    exact hz
  have hBC : B.subgroupOf J ≤ C :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hb : (B.subgroupOf J).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q,QuotientGroup.ker_mk'] using hBC
  apply hcomp.isCComponent.ne_bot
  change ((B.subgroupOf J).map q).subgroupOf _ = ⊥
  rw [hb,bot_subgroupOf]

/-- The literal source chief budget gives both the actor bound and the exact
intrinsic component layer. Baumann escape is the remaining producer of the budget. -/
theorem ordinary_selected_block_layer_of_chief_budget
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hescape : ¬ H ≤ M)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
      (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K)
    (hcount : ∀ s : ChiefSeries (sourceOne L T P),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2) :
    ⁅(Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T).pCoreIn 2,
      sourceOne L T P⁆ ≤ Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T ∧
    (ChapterC.blockU (K.map H.subtype)).map (K.map H.subtype).subtype =
      Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T := by
  have hTK := (h1332 _ hf).1
  have hmoved := ordinary_selected_moved_ne_bot_of_escape d h1221 hescape h1332 K hK hqK hf
  have hc := ordinary_selected_core_commutator_of_count d eL K hK hm hn hTK hgen hmoved hcount
  refine ⟨hc,?_⟩
  have hnG : sourceOne L T P ≤ normalizer (K.map H.subtype : Set G) := by
    have hh := (map_mono hn).trans (K.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hh
  have hgenG := congrArg (map H.subtype) hgen
  rw [map_commutator,map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hgenG
  have hp := Chapter1.Section02.Adequate.mem_L_isPPerfect
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mp hf).1
  exact ordinary_blockU_eq_moved_of_core_bound _ _ _ hp hnG hTK hgenG hc

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
