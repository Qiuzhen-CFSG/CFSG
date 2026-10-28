module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedModule
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Ahat6Centralizer
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Excluding the exceptional triple-six source component

The preimage P of the center of C/O₂(C) is a solvable I-invariant subgroup.
The source invariant-subgroup dichotomy either places the first residual in
P or makes P centralize the original plane V. In the first case the two
parabolics generate a solvable group, contradicting the quasisimple block
quotient. In the second case the central cubic norm forces V to be trivial.

The canonical generated-group consumer supplies the same C, first residual,
second parabolic and plane containment from the original 14.6 setup. No
classification or reconstruction statement is assumed beyond the exceptional
block alternative being eliminated.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029, and C.1.22, printed p.129.
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

/-- The exceptional triple-six block is impossible in the original parabolic setup. -/
theorem source_parabolic_not_exceptionalTripleSix
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 C : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2)
    (hI2quot : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I)
    (hCI : C ≤ I) (hCN : (C.subgroupOf I).Normal)
    (hVU : localModule T M ≤ (ChapterC.blockU C).map C.subtype)
    (hblock : ChapterC.IsExceptionalAhat6Block C) : False := by
  let P := C.coreCenterIn 2
  have hPI : P ≤ I := (coreCenterIn_le 2 C).trans hCI
  have hIC : I ≤ normalizer (C : Set G) := (normal_subgroupOf_iff_le_normalizer hCI).mp hCN
  have hIP : I ≤ normalizer (P : Set G) := hIC.trans (normalizer_le_normalizer_coreCenterIn 2 C)
  let : Group.IsSolvable (Subgroup.upperCentralSeriesStep (pCore 2 C)) := hblock.1.coreCenter_solvable
  let : Group.IsSolvable P := Group.isSolvable_of_surjective
    (C.subtype.subgroupMap_surjective (Subgroup.upperCentralSeriesStep (pCore 2 C)))
  have hI1I : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I) ≤ I :=
    sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  rcases source_invariant_solvable_subgroup_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I P hI
    hout hPI (hI1I.trans hIP) with hLP | hPC
  · have hI2I : I2 ≤ I := hgen ▸ le_sup_right
    let : Group.IsSolvable I2 := SymmetricThreeTwoCore.solvable hI2quot.some
    let : (P.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hIP
    let : Group.IsSolvable (P.subgroupOf I) := Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hPI).toMonoidHom) (subgroupOfEquivOfLe hPI).injective
    let : Group.IsSolvable (I2.subgroupOf I) := Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hI2I).toMonoidHom) (subgroupOfEquivOfLe hI2I).injective
    have hjoin : P ⊔ I2 = I := by
      apply le_antisymm (sup_le hPI hI2I)
      rw [←hgen]
      exact sup_le (sup_le (hLP.trans le_sup_left) (hSI2.trans le_sup_right)) le_sup_right
    let : Group.IsSolvable I := Group.isSolvable_of_normal_sup_eq_top
      (P.subgroupOf I) (I2.subgroupOf I) (by
        rw [←subgroupOf_sup hPI hI2I,hjoin,subgroupOf_self])
    let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective (inclusion_injective hCI)
    let : Group.IsSolvable (C ⧸ pCore 2 C) := Group.isSolvable_of_surjective
      (QuotientGroup.mk'_surjective (pCore 2 C))
    let : IsQuasisimple (C ⧸ pCore 2 C) := hblock.2.1
    let : IsSimpleGroup ((C ⧸ pCore 2 C) ⧸ center (C ⧸ pCore 2 C)) := IsQuasisimple.simple
    let : Nontrivial (C ⧸ pCore 2 C) := (QuotientGroup.mk'_surjective (center _)).nontrivial
    exact Group.IsPerfect.not_isSolvable (C ⧸ pCore 2 C) inferInstance
  · have hbot : localModule T M = ⊥ := by
      apply le_bot_iff.mp
      intro v hv
      obtain ⟨v,hvU,rfl⟩ := hVU hv
      have he := hblock.fixed_coreCenter_eq_one (⟨v,hvU⟩ : ChapterC.blockU C) (by
        intro x hx
        apply Subtype.ext
        exact ((hPC (mem_map_of_mem C.subtype hx)).2 v hv).symm)
      exact congrArg (fun z : ChapterC.blockU C => ((z : C) : G)) he
    rw [hbot,Subgroup.card_bot] at hcard
    omega

/-- The selected component of the canonical generated source group is not an Ahat6 block. -/
theorem source_generated_parabolic_not_exceptionalTripleSix
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
    let C := (pResidual 2 I0).map I0.subtype
    ¬ ChapterC.IsExceptionalAhat6Block C := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let L := sourceResidual M Mc
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let S := (T : Subgroup G) ⊓ I
  let I2 := (pResidual 2 H2).map H2.subtype ⊔ S
  let I0 := (R ⊔ S) ⊔ I2
  dsimp only
  intro hblock
  obtain ⟨hI0,hS,hgen,_,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
    ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  have hSI2 : (T : Subgroup G) ⊓ I0 ≤ I2 := by
    rw [hS]
    exact le_sup_right
  have hS0 := source_suitable_intersection_le_quotientCentralizer hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct
  have hsecond := suitable_second_parabolic_data h u hu H2 S
    (le_inf inf_le_left hI.1.2.1) hS0 hi.1 hi.2.2.2.1
    hSylH2 hH2kernel hH2quot hlocal
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
  obtain ⟨K,_,hKN,_,_,hK,_,_,hmodule,_⟩ := source_generated_parabolic_module_data
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  subst K
  let C := (pResidual 2 I0).map I0.subtype
  have hCI : C ≤ I0 := map_subtype_le _
  have hCN : (C.subgroupOf I0).Normal := by
    change (Subgroup.comap I0.subtype ((pResidual 2 I0).map I0.subtype)).Normal
    rw [comap_map_eq_self_of_injective I0.subtype_injective]
    exact hKN
  have hVW : localModule T M ≤ (ChapterC.blockU C).map C.subtype :=
    (le_conjugateSpanBy _ I0).trans hmodule.2
  exact source_parabolic_not_exceptionalTripleSix hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I0 I2 C hI0 hout0
    hSI2 hsecond.2.1 hgen hCI hCN hVW hblock
end CFSG.Quasithin.Chapter14.Section06
