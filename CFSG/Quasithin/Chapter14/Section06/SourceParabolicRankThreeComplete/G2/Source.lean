module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Reconstruction
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Intrinsic
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Flag
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Span
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Reduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The derived-G₂ second-parabolic branch

The original generated component contains the full plane span in its U-layer.
Its normality supplies a component Sylow from the actual intersection with T.
The recomputed first residual generates V, and the original second parabolic
centralizes Z and moves V. Thus the original source realizes every local
input to the G₂ flag calculation, without assuming singularity or rank three.

Whole-core reconstruction is the sole earlier classification input here.
The natural/Weyl cover describes the entire intrinsic U and retains its
literal conjugation. The flag calculation recognizes the doubly singular
plane and confines its conjugates to the point's three-dimensional pencil.
Movement then gives order eight and rank three for the literal source span.
The final adapter discharges Reduction's G₂ branch, retaining its independent
catalogue, binary-linear, alternating-seven and A₆-reconstruction premises.
Source: Aschbacher--Smith, original 14.6.10(5), printed p.1029.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open G2SecondParabolic ChapterC
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hg : G2ReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))
    (he : Nonempty ((sourceGeneratedComponent T M Mc I d.H2 ⧸
      pCore 2 (sourceGeneratedComponent T M Mc I d.H2)) ≃*
        commutator (Atlas.G2.Model (ZMod 2))))

include hg hI he

/-- Construct the actual point, plane, component Sylow and first-residual
movement inputs. In particular, no doubly singular flag is assumed. -/
theorem source_second_parabolic_g2_flag :
    FlagData (sourceGeneratedComponent T M Mc I d.H2)
      (localModule T M) (centralInvolutions T) (sourceSecondParabolic T I d.H2) := by
  let I0 := sourceGeneratedParabolic T M Mc I d.H2
  let C := sourceGeneratedComponent T M Mc I d.H2
  let J := sourceSecondParabolic T I d.H2
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨K,_,_,_,_,hres,_,hAC,hU,_⟩ := source_generated_parabolic_module_data
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  subst K
  obtain ⟨hI0,_,_,hJH2,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal
    ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
    ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput
    I d.H2 hI hout d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  have hCI : C ≤ I0 := map_subtype_le _
  have hIC : I0 ≤ normalizer (C : Set G) := I0.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I0 (pResidual 2 I0))
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
    d.local_normalizer hlocal I0 hI0.1).1
  have hn : (C.subgroupOf I0).Normal := normal_subgroupOf_of_le_normalizer hIC
  obtain ⟨S,hSC⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hCI
    hn.isSubnormal
  have hST : (S : Subgroup C).map C.subtype ≤ (T : Subgroup G) :=
    hSC.le.trans (inf_le_left.trans inf_le_left)
  have hTV : (T : Subgroup G) ≤ normalizer (localModule T M : Set G) :=
    hM.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  have hTZ : (T : Subgroup G) ≤ normalizer (centralInvolutions T : Set G) :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hH2H : d.H2 ≤ H := fun x hx =>
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H d.mem_span))).mp
      (d.le_quotient_centralizer hx)).1
  have hJM : ¬ J ≤ M := by
    intro hh
    apply hI0.1.2.2.2
    exact sup_le (sup_le (((map_subtype_le _).trans inf_le_left).trans
      (sourceResidual_le M Mc)) (inf_le_left.trans hM.1.2)) hh
  refine ⟨source_second_parabolic_g2_block_of_reconstruction
      hG T hempty hM hunique hmany hcard e hab hg H hH d I hI he,
    (le_conjugateSpanBy _ I0).trans hU.2, le_conjugateSpanBy _ _, hcard,
    plane_centralInvolutions_card T M hM.1.2 hcard e,
    ⟨S,hST.trans hTV,hST.trans hTZ⟩, ?_, le_sup_right.trans hIC, ?_, ?_⟩
  · refine ⟨(pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
      (sourceResidual M Mc ⊓ I0).subtype, hAC, ?_⟩
    exact source_parabolic_plane_moved hG T hempty hM hunique hmany hcard e hab
      H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
      d.local_normalizer hlocal I0 hI0.1
      (source_second_parabolic_intersection_escape
        hG T hempty hM hunique hmany hcard e hab H hH d I0 hI0)
  · exact (hJH2.trans hH2H).trans
      (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
        H hH.1 hH.2).2
  · rwa [← InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]

/-- Apply the whole-intrinsic-module cover to the actual generated component.
Both its projection and its action are the ones determined by reconstruction. -/
theorem source_second_parabolic_g2_whole_module :
    let C := sourceGeneratedComponent T M Mc I d.H2
    ∃ (hs : IsShort C) (m : BlockModuleModel C g2TwoNaturalAction),
      letI := hs.elementary
      ∃ f : (Atlas.G2.Natural.OrthogonalCover.binaryAction (ZMod 2)).IntertwiningMap
          (intrinsicAction hs m), Function.Surjective f ∧
        ∀ w, intrinsicProjection m (f w) = Atlas.G2.Natural.mk (ZMod 2) w := by
  have hb := (source_second_parabolic_g2_flag
    hG T hempty hM hunique hmany hcard e hab hg H hH d I hI he).block
  obtain ⟨m⟩ := hb.natural_model
  refine ⟨hb.short, m, ?_⟩
  let := hb.short.elementary
  exact intrinsic_weyl_cover hb.short m

/-- The actual second-parabolic span is elementary of order eight and rank
three. Its geometric marking is derived from the source flag inputs. -/
theorem source_second_parabolic_g2_span :
    IsElementaryAbelian 2
        (conjugateSpanBy (localModule T M) (sourceSecondParabolic T I d.H2)) ∧
      Nat.card (conjugateSpanBy (localModule T M) (sourceSecondParabolic T I d.H2)) = 8 ∧
      primeRank 2 (conjugateSpanBy (localModule T M) (sourceSecondParabolic T I d.H2)) = 3 := by
  exact flag_span (source_second_parabolic_g2_flag
    hG T hempty hM hunique hmany hcard e hab hg H hH d I hI he)

omit hI he in
/-- The derived-G₂ branch of original 14.6.10(5), conditional only on the
independent whole-core reconstruction. The unchanged branch contract retains
the original IStar choice and preferred-centralizer condition. -/
theorem source_second_parabolic_g2_rank_three_of_reconstruction :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2)))) := by
  intro H hH d I hI _ he
  exact (source_second_parabolic_g2_span
    hG T hempty hM hunique hmany hcard e hab hg H hH d I hI he).2.2

omit hI he in
/-- Supply the G₂ premise of the literal rank-three assembly. The other
source branches and A₆ reconstruction remain the assembly owner's inputs. -/
theorem source_second_parabolic_rank_three_of_g2_reconstruction
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hmodels : SourceSecondParabolicModelInput hG T hempty hM hunique hmany hcard e hab)
    (hbinary : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))))
    (hseven : SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7)))) :
    SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab := by
  exact source_second_parabolic_rank_three_of_model_branches
    hG T hempty hM hunique hmany hcard e hab ha hmodels hbinary hseven
      (source_second_parabolic_g2_rank_three_of_reconstruction
        hG T hempty hM hunique hmany hcard e hab hg)

end CFSG.Quasithin.Chapter14.Section06
