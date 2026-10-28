module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentRecognitionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredNatural
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic

/-!
# The covered natural exclusion and original component rows at G,T

The marked natural point centralizer above the cubic A₆ cover has three-rank
two. Reciprocal residual equality forces the original component to be covered
as well and identifies the same literal point radical on both sides. In the
selected component, a transposition would invert the cubic center, whereas
the point radical fixes it. The intrinsic offender calculation therefore
makes its Thompson subgroup centralize the natural module. The exact Sylow
centralizer yields the Baumann equality, contradicting the original covered
Baumann normalizer bound.

This specializes Nonsolvable/ComponentCoveredNaturalPoint and
ComponentCoveredNatural to structural facts at this same G,T, reusing the
intrinsic model and offender arguments. Combining all component exclusions
leaves just L₃(2) and ordinary A₆ in the original 13.3.2 list. The final
application constructs the augmentation marking, Chapter 12 guard, omega
fixed index and escaping relatively normal component from the original
five-dimensional module. It applies separately at every nonsolvable escaping
point; nonsolvability at other points is not inferred.

The linear-three module geometry, general amalgam and final recognition are
still required. The genuine 12.2/13.3 and natural LargeDistanceInput premises
retain their producers and final discharge. Source: Aschbacher--Smith
13.2.2(8),13.4.10(1--3), printed pp.877--878,907--908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionQuotients.FiveSeed.BarMarking
open ChapterB.QuasisimpleSource Chapter1.Section02.LocalModels
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V U : Subgroup G}

/-- The actual covered natural component forces the original augmentation component to be covered. -/
theorem covered_original_of_natural_component_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (DK : ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆)
    (q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6))
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G)),
      (e ((⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G).normalizerMonoidHom
        ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
            (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd) :
    Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      2 ≤ primeRank 3 (Solvable.firstCentralizerResidual L z.val) ∧
      Solvable.firstCentralizerResidual K m.constant.val =
        Solvable.firstCentralizerResidual L z.val := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  let qZ := (centralPreimageQuotientEquiv (pCore 2 K)).symm.trans q
  have hrec := six_component_reciprocal_residual_at h₀ h structural D m hzT hz1 hK hKN
    (component_quotient_quasisimple h1332 hfK) qZ
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point_at h₀ h structural m hzT hz1 hK.1
    (h1332 K hfK).1 hKM
  have hr := (covered_natural_point_structure DK hc q e he w hw).1
  rw [←hC,←Solvable.firstCentralizerResidual_threeRank,hrec] at hr
  refine ⟨?_,hr,hrec⟩
  let := h.quasisimple
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) :=
    Nat.not_even_iff_odd.mp (fun hh => hn (even_iff_two_dvd.mp hh))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
      (augmentationCentralQuotient D m) ho with hcL | ⟨_,hcL⟩
  · let eL := GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (augmentationCentralQuotient D m) hcL
    have hu := core_component_point_threeRank_le_one D m eL z hzL
    rw [←Solvable.firstCentralizerResidual_threeRank] at hu
    omega
  · exact hcL

/-- The two covered components have the same literal point parabolic and radical. -/
theorem covered_natural_component_common_point_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (DK : ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆)
    (q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6))
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G)),
      (e ((⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G).normalizerMonoidHom
        ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
            (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd) :
    Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      ∃ w : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G),
        w ≠ 1 ∧ (T : Subgroup G) ≤ centralizer ({w.val} : Set G) ∧
        Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) =
          (K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G) ∧
        normalizer (ChapterB.baumann
          (((K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G)).pCoreIn 2) : Set G) ≤
          normalizer (L : Set G) := by
  obtain ⟨hcL,_,hrec⟩ := covered_original_of_natural_component_at h₀ h structural D m h1332
    z hzT hzL hK hKN hKM hfK hc DK q e he
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  obtain ⟨w,hw,hTw,hpoint⟩ := component_fixed_generator_point_overgroup_at
    h₀ h structural m hzT hz1 hK.1 (h1332 K hfK).1 hKM
  have hC : K ⊓ centralizer ({m.constant.val} : Set G) =
      K ⊓ centralizer ({w.val} : Set G) := by
    have hh := congrArg (fun B : Subgroup G => K ⊓ B) hpoint
    simpa only [←inf_assoc,inf_eq_left.mpr (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)] using hh
  have h23 := (covered_natural_point_structure DK hc q e he w hw).2
  have hP : Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) =
      (K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G) := by
    rw [←hrec,Solvable.firstCentralizerResidual_eq,hC,
      ←twoResidual_eq_primeToResidual_three h23]
    exact embedded_pointResidual_sup_sylow T K (h1332 K hfK).1 w.val hTw
  refine ⟨hcL,w,hw,hTw,hP,?_⟩
  rw [←hP]
  exact covered_augmentation_baumann_normalizer_at h structural D m hcL z hzT hzL

/-- The marked covered natural point radical has the Thompson and Baumann subgroups of O₂(KT). -/
theorem covered_natural_point_thompson_baumann_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6))
    (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : U),
      (e (U.normalizerMonoidHom ⟨k.val,D.normalizes k.property⟩ v)).toAdd =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
          (a (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (w : U) (hw : w ≠ 1) (hTw : (T : Subgroup G) ≤ centralizer ({w.val} : Set G)) :
    let R := ((K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G)).pCoreIn 2
    let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ Q ∧
      ChapterB.baumann R = ChapterB.baumann Q := by
  let X := K ⊔ (T : Subgroup G)
  let P := X ⊓ centralizer ({w.val} : Set G)
  let R := P.pCoreIn 2
  let Q := X.pCoreIn 2
  have hPX : P ≤ X := inf_le_left
  have hTP : (T : Subgroup G) ≤ P := le_inf le_sup_right hTw
  have hRX : R ≤ X := (pCoreIn_le 2 P).trans hPX
  have hRT : R ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 P).le_sylow_of_normalized T
      (hTP.trans (P.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image P (pCore 2 P))))
  have hQR : Q ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X)
    (le_inf (pCoreIn_le 2 X)
      (D.core_centralizes.trans (centralizer_le (Set.singleton_subset_iff.mpr w.property))))
    (hPX.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hXU : X ≤ normalizer (U : Set G) := sup_le D.normalizes ((structural K h).2.2 U D).1
  have hXK : X ≤ normalizer (K : Set G) := sup_le K.le_normalizer D.sylow_normalizes_component
  let := D.elementary
  let lin : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    e.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  let α := a.toMonoidHom.comp (QuotientGroup.mk' (centralCore K))
  obtain ⟨q,hqL,hqU,_⟩ := natural_extension X K U le_sup_left hXK hXU α
    (a.surjective.comp (QuotientGroup.mk'_surjective _)) lin
      (fun k v => he k v.toMul)
  have hUX : U ≤ X := D.le_sylow.trans le_sup_right
  let W := U.subgroupOf X
  let : W.Normal := normal_subgroupOf_of_le_normalizer hXU
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hUX
  let eu : W ≃* U := subgroupOfEquivOfLe hUX
  let eW := eu.trans e
  let wi := eu.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by
    simpa only [wi,eu.apply_symm_apply,map_one] using congrArg eu hh)
  have heW (x : X) (v : W) : (eW (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q x) (eW v).toAdd :=
    hqU x (Additive.ofMul (eu v))
  have hY : alternatingGroup (Fin 6) ≤ q.range := by
    intro b hb
    obtain ⟨c,hc⟩ := a.surjective ⟨b,hb⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (centralCore K) c
    exact ⟨inclusion le_sup_left k,(hqL k).trans (congrArg Subtype.val hc)⟩
  let C := centralizer ({wi.val} : Set X)
  have hCm : C.map X.subtype = P := by
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hRm : (C.pCoreIn 2).map X.subtype = R := by
    rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective,hCm]
  let := h.quasisimple
  have hJWC := CoveredNaturalThompson.point_radical_thompson_centralizes W q eW heW hY wi hwi
    (fun x hx => CoveredNaturalAction.point_core_no_swap D a e he hc q hqL w x (by
      change x.val ∈ R
      rw [←hRm]
      exact mem_map_of_mem X.subtype hx))
  have hJUC : elementaryAbelianMaxJ R ≤ centralizer (U : Set G) := by
    rw [←hRm,elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective]
    rintro _ ⟨x,hx,rfl⟩ v hv
    exact congrArg Subtype.val (hJWC hx ⟨v,hUX hv⟩ hv)
  have hCQ : (T : Subgroup G) ⊓ centralizer (U : Set G) = Q :=
    RecognitionSource.chosen_sylow_centralizer_eq_core_at h D structural
  have hJQ : elementaryAbelianMaxJ R ≤ Q := by
    rw [←hCQ]
    exact le_inf ((sSup_le fun A hA => hA.1).trans hRT) hJUC
  have hJ : elementaryAbelianMaxJ R = elementaryAbelianMaxJ Q :=
    (elementaryAbelianMaxJ_eq_of_intermediate R Q hJQ hQR).symm
  refine ⟨hJ,?_⟩
  have hJQQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
  have hUZ : U ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ Q) :=
    elementary_centralizer_maxJ_le_omegaCenter Q U D.le_core
      ((le_centralizer_iff.mp D.core_centralizes).trans (centralizer_le hJQQ))
  change R ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ R) : Set G) =
    Q ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G)
  rw [hJ]
  apply le_antisymm
  · exact (le_inf (le_inf (inf_le_left.trans hRT)
      (inf_le_right.trans (centralizer_le hUZ)) |>.trans hCQ.le) inf_le_right)
  · exact inf_le_inf_right _ hQR

/-- Exclude the fixed-free natural covered row on the actual selected component. -/
theorem covered_natural_component_excluded_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (DK : ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆)
    (q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6))
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G)),
      (e ((⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G).normalizerMonoidHom
        ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
            (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd) :
    False := by
  obtain ⟨_,w,hw,hTw,_,hB⟩ := covered_natural_component_common_point_at
    h₀ h structural D m h1332 z hzT hzL hK hKN hKM hfK hc DK q e he
  have hqK := component_quotient_quasisimple h1332 hfK
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩ hqK
  have hb := (covered_natural_point_thompson_baumann_at hK12 structural DK q e he hc w hw hTw).2
  let X := K ⊔ (T : Subgroup G)
  have hKB : K ≤ normalizer (ChapterB.baumann
      (((K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G)).pCoreIn 2) : Set G) := by
    rw [hb]
    exact (le_sup_left.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))).trans
        (normalizer_le_normalizer_baumann (X.pCoreIn 2))
  exact hKM (hKB.trans hB)

/-- The original selected component has ordinary A₆ or L₃(2) quotient, with all other rows excluded. -/
theorem selected_component_rows_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T) :
    Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
  rcases selected_component_recognition_at hl h₀ h structural D m h1332 fixed five
    covered h13316 hindex z hzT hzL hK hKN hKM hfK with h3 | h6 | ⟨hc,DK,_,_,q,e,he⟩
  · exact Or.inl h3
  · exact Or.inr h6
  · have hcc : Nat.card (center (K ⧸ pCore 2 K)) = 3 := by
      obtain ⟨_,⟨a⟩,_⟩ := hc
      rw [Nat.card_congr a.toEquiv]
      simp
    exact (covered_natural_component_excluded_at h₀ h structural D m h1332
      z hzT hzL hK hKN hKM hfK hcc DK q e he).elim

/-- Construct a relatively normal escaping component with one of the two source quotients at every original nonsolvable escaping point. -/
theorem original_escaping_component_rows_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G))) :
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      K ∈ Chapter1.LStar G T ∧
      centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      ¬ L ≤ normalizer (K : Set G) ∧
      (Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))) := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  have hindex := original_omega_fixed_index_at h₀ h structural D m earlier
  obtain ⟨K,hK,hfK,hstarK,hKN,hTK,hKM,hLK⟩ :=
    augmentation_exists_escaping_component_at h₀ h structural m h1332 hzT
      (fun he => hzL (he ▸ one_mem _)) hout hnonsolv
  exact ⟨K,hK,hfK,hstarK,hKN,hTK,hKM,hLK,
    selected_component_rows_at hl h₀ h structural D m h1332 fixed five covered
      h13316 hindex z hzT hzL hK hKN hKM hfK⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
