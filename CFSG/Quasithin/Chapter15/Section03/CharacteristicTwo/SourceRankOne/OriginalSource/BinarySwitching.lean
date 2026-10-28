module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryFirstPlane
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryLargeCenter
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.FixedLineComponent

/-!
# Switching the original large binary branch to its fixed-line centralizer

The first-plane calculation makes the original component L centralize the
actual line Z_S ∩ V₁. Consequently its centralizer contains I=LS and belongs
to the original outside family. The proved source 15.3.11 gives the same Sylow
subgroup S there. The full-catalogue local containment theorem supplies a unique
normal C-component containing L in this centralizer.

The MS center model comes from the actual common and earlier core-factor facts;
no original-two-core fixation or C_I(Y₊) action premise is retained. Identifying
or excluding the resulting containing component remains a separate source step.

Source: Aschbacher--Smith 15.3.11, 15.3.31--32 and 1.2.4,
printed pp.1124,1132--1133 and505.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration EightGeometry
open SmallExtension SmallExtension.CentralCover SmallExtension.CentralCover.LinearThree
open ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The actual first-line centralizer and its unique containing normal component,
using only a natural center model at the original small source configuration. -/
theorem source_binary_switching_of_centerModel
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (m : CenterModel c.L natural) :
    let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
    I ≤ C ∧ C ∈ d.Hplus ∧ ∃ T : Sylow 2 C,
      (T : Subgroup C).map C.subtype = d.S ∧
      ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
        ∀ D : Subgroup C, D.IsCComponent → c.L.subgroupOf C ≤ D → D = K := by
  let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
  have hfixed := BinaryFirstPlane.firstLine_fixed_eq_of_centerModel s hm m
  have hcard := BinaryFirstPlane.firstLine_card (d := d)
  have hIC : I ≤ C := overgroup_le_fixedLine_centralizer d c s.generated hfixed
  have hC : C ∈ d.Hplus := fixedLine_centralizer_mem_outside d s.minimal.1 c
    s.generated hfixed hcard
  have h11 : ∀ J ∈ d.Hplus, Chapter1.IsSylowIn 2 d.S J := by
    intro J hJ
    exact (OutsideStructure.source_lemma_15_3_11_from_selection
      hG d hempty hM hu hmany J hJ).sylow
  obtain ⟨T,hT⟩ := h11 C hC
  have hSC : d.S ≤ C := hT ▸ map_subtype_le (T : Subgroup C)
  have hLC : c.L ≤ C := (component_le c).trans hIC
  have hTeq : (T : Subgroup C) = d.S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hSC]
    exact hT
  have hB : c.L.subgroupOf C ∈ Chapter1.L C T := by
    rw [hTeq]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSC hLC).mp
      (component_mem_fixedLine_local_family d s.minimal.1 c s.normal s.generated hfixed h11)
  have hSL : d.S ≤ normalizer (c.L : Set G) :=
    (show d.S ≤ I from s.generated ▸ le_sup_right).trans
      ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp s.normal)
  have hTB : (T : Subgroup C) ≤ normalizer (c.L.subgroupOf C : Set C) := by
    rw [hTeq, ← subgroupOf_normalizer_eq hLC]
    exact comap_mono hSL
  obtain ⟨K,⟨hK,hBK,hKn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (fixedLine_centralizer_quotient_sqtk hG d hcard) T hB hTB
  refine ⟨hIC,hC,T,hT,K,hK,hKn,hBK,?_⟩
  obtain ⟨K',⟨hK',hBK'⟩,huniq⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
      (fun _ _ _ => ChapterA.Section03.SourceComponents.containment_knownSimple)
      (fixedLine_centralizer_quotient_sqtk hG d hcard) T hB
  intro D hD hBD
  exact (huniq D ⟨hD,hBD⟩).trans (huniq K ⟨hK,hBK⟩).symm

/-- The original large-distance MS core supplies the center model and therefore
all local-family and normal-component data for fixed-line switching. -/
theorem source_binary_large_switching
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* LinearThree.SL)
    (t : InputSetup (source_binaryMSInput s e))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
    I ≤ C ∧ C ∈ d.Hplus ∧ ∃ T : Sylow 2 C,
      (T : Subgroup C).map C.subtype = d.S ∧
      ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
        ∀ D : Subgroup C, D.IsCComponent → c.L.subgroupOf C ≤ D → D = K := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (c.L ⧸ pCore 2 c.L) := (e.trans Matrix.PSL3Two.equiv).isSimpleGroup
  exact source_binary_switching_of_centerModel hG hempty hM hu hmany s hm
    (source_binary_large_centerModel s e t common earlier)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
