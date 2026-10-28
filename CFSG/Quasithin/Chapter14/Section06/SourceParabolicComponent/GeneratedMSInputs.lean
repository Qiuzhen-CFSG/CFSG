module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedModule
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSInputs

/-!
# The MS inputs on the literal generated parabolic

The canonical generated group I₀ has the C.2.7 input on C = O²(I₀).
Its first parabolic lies in I₀ ∩ M and contains the full Sylow intersection,
so it is a proper odd-index subgroup with the specified two-core R₁.
Characteristic-normalizer control supplies MS3 on this same R₁ in I₀.
Thus both structural MS inputs are consequences of the original source
hypotheses, before any alternating-block or module reconstruction.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029, using C.1.31
and C.2.3--C.2.7, printed pp.135 and 144--147.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
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

/-- The original generated first two-core satisfies MS2(a) and MS3. -/
theorem source_generated_parabolic_ms_inputs
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
      (conjugateSpanBy (localModule T M) H))) :
    let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
    let I0 := ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
      (sourceResidual M Mc ⊓ I0).subtype ⊔ ((T : Subgroup G) ⊓ I0)
    let C := (pResidual 2 I0).map I0.subtype
    Input KnownSimple.IsKnownSimple I0 (I1.pCoreIn 2) (I0 ⊓ M) C ∧
      ChapterC.MSOddIndexRadical ((I1.pCoreIn 2).subgroupOf I0) ∧
      ChapterC.MSCharacteristicCondition ((I1.pCoreIn 2).subgroupOf I0) := by
  let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
  let I0 := ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
  let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
    (sourceResidual M Mc ⊓ I0).subtype ⊔ ((T : Subgroup G) ⊓ I0)
  dsimp only
  obtain ⟨K,_,_,_,_,hres,_,_,_,_,_,_,hi,_⟩ := source_generated_parabolic_module_data
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  subst K
  have hI1I : I1 ≤ I0 := sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  have hI1M : I1 ≤ I0 ⊓ M := le_inf hI1I
    (sup_le (((map_subtype_le _).trans inf_le_left).trans (sourceResidual_le M Mc))
      (inf_le_left.trans hM.1.2))
  obtain ⟨hI0,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
    ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput
    I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  obtain ⟨S,hS⟩ := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I0 hI0.1).1
  have hSI1 : (S : Subgroup I0) ≤ I1.subgroupOf I0 := by
    intro s hs
    have hs' : (s : G) ∈ (T : Subgroup G) ⊓ I0 := hS ▸ mem_map_of_mem I0.subtype hs
    exact mem_sup_right hs'
  exact ⟨hi,ChapterC.C27Source.msOddIndexRadical_of_first_core hi I1 hI1I hI1M S hSI1 rfl,
    ChapterC.C27Source.msCharacteristic_from_source hi⟩
end CFSG.Quasithin.Chapter14.Section06
