module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixPlacement.FixedCore
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedModule

/-!
# Fixed-core placement for the literal generated group

The source I₀ retains the maximal Sylow intersection and the preferred
centralizer condition from original14.6.10(5). The extra residual O²(H₂)
centralizes u because its modulo-point commutator character has two-group
image. Thus the fixed-core placement theorem applies to this same I₀ and
its actual component C=O²(I₀). The remaining fixed-vector marks are the
full-core geometry inputs, not an independently chosen module.

Source: Aschbacher–Smith, original14.6.10(5), printed pp.1029–1030.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSixPlacement
universe u
open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {G : Type u} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal

/-- Original placement for the actual generated parabolic and its full core. -/
theorem source_generated_fixed_core_vector_placement
    (I H2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hSylH2 : Chapter1.IsSylowIn 2 (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u) H2)
    (hH2kernel : H2 ≤
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).kernel (zpowers u))
    (hH2quot : Nonempty ((H2 ⧸ pCore 2 H2) ≃* Equiv.Perm (Fin 3)))
    (hH2out : ¬ H2 ≤ M)
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (hpreferred : (T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({u} : Set G) →
      I ≤ centralizer ({u} : Set G)) :
    let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
    let I0 := ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
    let C := (pResidual 2 I0).map I0.subtype
    ∀ a : G, a ∈ conjugateSpanBy (localModule T M) I2 →
      a ∈ (ChapterC.blockU C).map C.subtype → a ≠ 1 →
      I0 ≤ centralizer ({a} : Set G) →
      (T : Subgroup G) ⊓ I0 = (T : Subgroup G) ⊓ centralizer ({u} : Set G) ∧
      I0 ≤ centralizer ({u} : Set G) ∧ u ∈ (ChapterC.blockU C).map C.subtype := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let L := sourceResidual M Mc
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let S := (T : Subgroup G) ⊓ I
  let I2 := (pResidual 2 H2).map H2.subtype ⊔ S
  let I0 := (R ⊔ S) ⊔ I2
  dsimp only
  intro a ha haW hane hIa
  obtain ⟨hI0,hS,hgen,hI2H2,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
    ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  have hH2H : H2 ≤ H := fun x hx =>
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp (hH2kernel hx)).1
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  have hRout := (source_intersection_parabolic_data hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover).2.2.2
  have hout0 : ¬ I0 ⊓ M ≤ Mc := by
    intro hh
    apply hRout
    exact (le_inf (le_sup_left.trans le_sup_left)
      (((map_subtype_le _).trans inf_le_left).trans (sourceResidual_le M Mc))).trans hh
  have hpreferred0 : (T : Subgroup G) ⊓ I0 =
      (T : Subgroup G) ⊓ centralizer ({u} : Set G) → I0 ≤ centralizer ({u} : Set G) := by
    intro hs
    have hsI : S = (T : Subgroup G) ⊓ centralizer ({u} : Set G) := hS.symm.trans hs
    have hIu := hpreferred hsI
    have hRu : R ≤ centralizer ({u} : Set G) :=
      ((map_subtype_le _).trans inf_le_right).trans hIu
    have hSu : S ≤ centralizer ({u} : Set G) := hsI ▸ inf_le_right
    exact sup_le (sup_le hRu hSu)
      (sup_le (residual_kernel_centralizes h u hu H2 hH2kernel) hSu)
  exact source_fixed_core_vector_placement hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct hU3 hlocal I0 _ hI0 hout0 hpreferred0 a
    (conjugateSpanBy_mono le_rfl (hI2H2.trans hH2H) ha) haW hane hIa

end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSixPlacement
