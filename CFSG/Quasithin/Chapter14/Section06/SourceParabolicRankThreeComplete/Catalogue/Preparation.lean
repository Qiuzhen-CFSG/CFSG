module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.Inputs
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedModule
public import CFSG.Quasithin.Chapter14.Section06.SourceClassificationComplete

/-!
# The catalogue input on the original generated residual

The original data supplies escape and the local Sylow condition. The selected
internal component is exactly O²(I₀); its inclusion identifies it with the
ambient generated component. This transports the F.6.18 exclusion of binary
SL₂ to the same carrier as the seven C.2.7 star markings.

Source: Aschbacher--Smith original 14.6.10(5), printed p.1029.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Both source catalogues concern the literal residual and its recomputed
first parabolic. No preferred-centralizer or module conclusion is used. -/
theorem prepared
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M)) :
    let I0 := sourceGeneratedParabolic T M Mc I d.H2
    let C := sourceGeneratedComponent T M Mc I d.H2
    Input KnownSimple.IsKnownSimple I0 (firstCore T M Mc I d.H2) (I0 ⊓ M) C ∧
      ChapterC.C27Source.SmallModels.Model (star T M Mc I d.H2) ∧
      (∀ F : BinaryField, ¬ Nonempty ((C ⧸ pCore 2 C) ≃* SL(2,F.Carrier))) := by
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨K,_,_,_,_,hres,_,_,_,_,hnb,_,hi,hm,_⟩ := source_generated_parabolic_module_data
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  subst K
  refine ⟨hi,hm,?_⟩
  intro F he
  obtain ⟨a⟩ := he
  let F' : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField :=
    { Carrier := F.Carrier, degree := F.degree, degree_pos := F.degree_pos, card_eq := F.card_eq }
  let I0 := sourceGeneratedParabolic T M Mc I d.H2
  let b := (pResidual 2 I0).equivMapOfInjective I0.subtype I0.subtype_injective
  exact hnb F' ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans a⟩

/-- The two catalogue markings retain the canonical comparison on every
original residual element, and its image is the whole generalized Fitting
subgroup. This is the input for excluding the larger linear models. -/
theorem compared
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M)) :
    let I0 := sourceGeneratedParabolic T M Mc I d.H2
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
      (sourceResidual M Mc ⊓ I0).subtype ⊔ ((T : Subgroup G) ⊓ I0)
    let K := pResidual 2 I0
    let q := QuotientGroup.mk' (pPrimeCore 3 I0)
    let A := (I1.subgroupOf I0).map q
    let B := ((sourceSecondParabolic T I d.H2).subgroupOf I0).map q
    ∃ S : Sylow 2 (I0 ⧸ pPrimeCore 3 I0), A ⊓ B = (S : Subgroup _) ∧
      (FSource.SourceAlternative A B S ∨ FSource.SourceAlternative B A S) ∧
      K.map q = generalizedFitting (I0 ⧸ pPrimeCore 3 I0) ∧
      IsQuasisimple (generalizedFitting (I0 ⧸ pPrimeCore 3 I0)) ∧
      ∃ a : (star T M Mc I d.H2 ⧸ center (star T M Mc I d.H2)) ≃*
          ((K.map q) ⧸ center (K.map q)),
        ∀ k : K, a (QuotientGroup.mk' (center (star T M Mc I d.H2))
          (toStarImage (sourceGeneratedComponent T M Mc I d.H2) (firstCore T M Mc I d.H2)
            (K.equivMapOfInjective I0.subtype I0.subtype_injective k))) =
          QuotientGroup.mk' (center (K.map q)) (q.subgroupMap K k) := by
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨K,_,_,_,_,hres,_,_,_,_,_,_,_,_,_,ha,S,hS,halt,hf,hq⟩ :=
    source_generated_parabolic_module_data
      hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
      d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
      d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
      d.core_index d.module_rank
  subst K
  exact ⟨S,hS,halt,hf,hq,ha⟩

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue
