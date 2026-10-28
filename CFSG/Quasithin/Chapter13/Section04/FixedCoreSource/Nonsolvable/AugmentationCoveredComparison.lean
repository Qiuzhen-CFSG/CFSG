module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationCoveredAction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCoreNoSwap
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAlternative
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationPrefix
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# The covered Thompson/Baumann comparison and full augmentation alternative

In the covered original row, the point radical has no transposition on the
five-dimensional augmentation module. Its maximal elementary subgroups
therefore centralize V. Since C_T(V)=O₂(LT), this proves
J(O₂(L₁T))=J(O₂(LT)). The module lies in the omega-center of the latter
Thompson subgroup, giving the corresponding Baumann equality.

Maximal two-local uniqueness now bounds the normalizer of the original
Baumann group, and of each of its nontrivial characteristic subgroups,
by N_G(L). Applying this to the covered branch and the previously checked
ordinary alternative to the other branch gives the full augmentation
Baumann/short-block alternative without an ordinary-A₆ hypothesis.
The natural LargeDistanceInput remains explicit only for that ordinary
branch; its producer is qt-e-ms-small-a6-exhaustion-large-distance.

The selected-component comparison inside K R(T∩K), the remaining covered-row
exclusions, reciprocal comparison, commutator and graph arguments remain
with qt-d-1341-nonsolvable-source. Universal nonsolvability at both escaping
weights and final earlier-input discharge remain with the original assembly;
this module does not assert the completed nonsolvable contradiction.
Source: Aschbacher–Smith 13.2.2(7–8), printed pp.877–878, used in 13.4.10,
printed pp.908–909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original covered augmentation row has the same Thompson and Baumann
subgroups in O₂(L₁T) as in O₂(LT), at either escaping weight. -/
theorem covered_augmentation_thompson_baumann
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ Q ∧
      ChapterB.baumann R = ChapterB.baumann Q := by
  let X := L ⊔ (T : Subgroup G)
  let P := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let Q := X.pCoreIn 2
  have hP : P = X ⊓ centralizer ({z.val} : Set G) :=
    covered_augmentation_point_parabolic D m hc z hzT hzL
  have hPX : P ≤ X := hP.le.trans inf_le_left
  have hRX : R ≤ X := (pCoreIn_le 2 P).trans hPX
  have hRT : R ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 P).le_sylow_of_normalized T
      (le_sup_right.trans (P.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image P (pCore 2 P))))
  have hQR : Q ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X)
    (by
      rw [hP]
      exact le_inf (pCoreIn_le 2 X)
        (D.core_centralizes.trans (centralizer_le (Set.singleton_subset_iff.mpr z.property))))
    (hPX.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hXV := sup_le D.normalizes (((structural G T L h).2.2 V D).1)
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  let U := V.subgroupOf X
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXV
  let := D.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  let zi := eu.symm z
  have hn := normalizer_component_le_module h structural D m
  obtain ⟨qN,hqN,hqNL,_⟩ := exists_core_normalizer_permutation D m hn
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  let q := qN.comp (inclusion hXN)
  have hqL (l : L) : q (inclusion (show L ≤ X from le_sup_left) l) =
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val := hqNL l
  have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd :=
    hqN (inclusion hXN x) (eu v)
  have hY : alternatingGroup (Fin 6) ≤ q.range := by
    intro a ha
    obtain ⟨b,hb⟩ := m.quotient.surjective ⟨a,ha⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) b
    exact ⟨inclusion le_sup_left l,(hqL l).trans (congrArg Subtype.val hb)⟩
  have hz : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (e zi).toAdd = (e zi).toAdd := by
    intro hz
    apply hzL
    apply (m.mem_fixed_iff z).mpr
    apply (BinaryPermutation.core_fixed_iff_constant (by simp) _).mp
    change ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.coreRepresentation (Fin 6) a.val (e zi).toAdd = (e zi).toAdd at hz
    simpa only [e,zi,MulEquiv.trans_apply,eu.apply_symm_apply] using hz
  let C := centralizer ({zi.val} : Set X)
  have hCm : C.map X.subtype = P := by
    rw [hP]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hRm : (C.pCoreIn 2).map X.subtype = R := by
    rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective,hCm]
  let := h.quasisimple
  have hJC := ChapterB.Offenders.SixCorePoint.pointRadical_thompson_centralizes_of_no_swap
    U q e he hY zi hz (fun x hx => covered_augmentation_point_core_no_swap D m hc q hqL z x (by
      change x.val ∈ (X ⊓ centralizer ({z.val} : Set G)).pCoreIn 2
      rw [←hP]
      change x.val ∈ R
      rw [←hRm]
      exact mem_map_of_mem X.subtype hx))
  have hJVC : elementaryAbelianMaxJ R ≤ centralizer (V : Set G) := by
    rw [←hRm,elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective]
    rintro _ ⟨x,hx,rfl⟩ v hv
    exact congrArg Subtype.val (hJC hx ⟨v,hVX hv⟩ hv)
  have hCQ : (T : Subgroup G) ⊓ centralizer (V : Set G) = Q :=
    RecognitionSource.chosen_sylow_centralizer_eq_core h D structural
  have hJQ : elementaryAbelianMaxJ R ≤ Q := by
    rw [←hCQ]
    exact le_inf ((sSup_le fun A hA => hA.1).trans hRT) hJVC
  have hJ : elementaryAbelianMaxJ R = elementaryAbelianMaxJ Q :=
    (elementaryAbelianMaxJ_eq_of_intermediate R Q hJQ hQR).symm
  refine ⟨hJ,?_⟩
  have hJQQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
  have hVZ : V ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ Q) :=
    elementary_centralizer_maxJ_le_omegaCenter Q V D.le_core
      ((le_centralizer_iff.mp D.core_centralizes).trans (centralizer_le hJQQ))
  change R ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ R) : Set G) =
    Q ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G)
  rw [hJ]
  apply le_antisymm
  · refine le_inf ?_ inf_le_right
    exact (le_inf (inf_le_left.trans hRT)
      (inf_le_right.trans (centralizer_le hVZ))).trans hCQ.le
  · exact inf_le_inf_right _ hQR
/-- In the covered original row the literal Baumann normalizer is contained
in N_G(L). Thus the covered source case cannot take the short-block escape
alternative of the ordinary augmentation argument. -/
theorem covered_augmentation_baumann_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) := by
  dsimp only
  rw [(covered_augmentation_thompson_baumann h structural D m hc z hzT hzL).2]
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  have hBQ : ChapterB.baumann Q ≤ Q := inf_le_left
  have hZJ : omegaOneCenterAmbient (elementaryAbelianMaxJ Q) ≤ elementaryAbelianMaxJ Q :=
    fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hZQ : omegaOneCenterAmbient (elementaryAbelianMaxJ Q) ≤ Q :=
    hZJ.trans (sSup_le fun _ hA => hA.1)
  have hVB : V ≤ ChapterB.baumann Q := le_inf D.le_core
    ((le_centralizer_iff.mp D.core_centralizes).trans (centralizer_le hZQ))
  have hBne : ChapterB.baumann Q ≠ ⊥ := fun hh => D.ne_bot (eq_bot_iff.mpr (hh ▸ hVB))
  have hXN : X ≤ normalizer (ChapterB.baumann Q : Set G) :=
    (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
      (normalizer_le_normalizer_baumann Q)
  exact normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    ((isPGroup_pCoreIn 2 X).to_le hBQ) hBne hXN

/-- Every nontrivial characteristic subgroup of the original covered Baumann
group has its normalizer in N_G(L), as required by the later C.1.37 application. -/
theorem covered_augmentation_characteristic_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (A : Subgroup G)
    (hAB : A ≤ ChapterB.baumann ((Solvable.firstCentralizerResidual L z.val ⊔
      (T : Subgroup G)).pCoreIn 2))
    (hchar : (A.subgroupOf (ChapterB.baumann ((Solvable.firstCentralizerResidual L z.val ⊔
      (T : Subgroup G)).pCoreIn 2))).Characteristic)
    (hne : A ≠ ⊥) : normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  let X := L ⊔ (T : Subgroup G)
  let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
  let B := ChapterB.baumann R
  have hb : B = ChapterB.baumann (X.pCoreIn 2) :=
    (covered_augmentation_thompson_baumann h structural D m hc z hzT hzL).2
  have hXB : X ≤ normalizer (B : Set G) := by
    rw [hb]
    exact (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
        (normalizer_le_normalizer_baumann (X.pCoreIn 2))
  let : (A.subgroupOf B).Characteristic := hchar
  have hBA := normalizer_le_normalizer_characteristic_image B (A.subgroupOf B)
  rw [map_subgroupOf_eq_of_le (show A ≤ B from hAB)] at hBA
  exact normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    ((isPGroup_pCoreIn 2 _).to_le (hAB.trans inf_le_left)) hne (hXB.trans hBA)

open Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion

/-- The full original five-dimensional Baumann/short-block alternative,
including the covered row. The independent natural large-distance input is
used only in the ordinary row. -/
theorem augmentation_baumann_alternative_of_largeDistance
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) ∨ ChapterC.IsShort L := by
  let := h.quasisimple
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) :=
    Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
    (augmentationCentralQuotient D m) ho with hc | ⟨_,hc⟩
  · let eL := GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (augmentationCentralQuotient D m) hc
    exact ordinary_augmentation_baumann_alternative_of_largeDistance hl h structural D m eL z hzT hzL
  · exact Or.inl (covered_augmentation_baumann_normalizer h structural D m hc z hzT hzL)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
