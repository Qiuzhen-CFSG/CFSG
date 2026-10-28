module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ClassifiedFactors
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.NormalClosureThree
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FiveSeed
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.RatioOne
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.CyclicJoin

/-!
# The original selected action's full ratio-factor reduction

All original starred-actor cases are discharged before restricting the module.
A noncyclic actor gives the proved three-core reduction. In the cyclic case,
ratio one has a three-group residual. At ratio two, each actor's normal closure
has two-group image modulo the ambient Fitting subgroup: the quintic case
uses its quintic residual, and the other case uses the ambient central seed
and the complete cyclic factor classification. Joining the original actors
therefore gives the required odd-Fitting/Sylow factorization of Jhat.

The actual Sylow-fixed generating seed now supplies a faithful fully
Fitting-moved Jhat action retaining exactly the original starred actors.
D.2.16 produces its finite family, and the completed source classification
constructs the ambient permutation of the original blocks and supports.
No full-movement, quotient-two, or factor-classification premise remains.

Source: Aschbacher--Smith 15.1.2, first paragraph, printed p.1084,
with D.2.16--29, printed pp.187--192.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.RatioDecomposition ChapterD.UniqueFactor
open ChapterA.Section05To06 Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The original centralizing action has a faithful, fully Fitting-moved
Jhat factor datum and finite indecomposable family. Every case is discharged
using the actual quotient cover and Sylow-fixed generating seed. -/
theorem source_centralizing_factor_decomposition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∃ (U : Submodule (ZMod 2) (Additive (localModule T M))) (c : FactorData ρ (Jhat ρ) U),
      subspaceCommutator c.representation ⊤ (fittingSubgroup (Jhat ρ)) = ⊤ ∧
        ∃ d : Decomposition c.representation, d.FittingFull := by
  classical
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let K := Jhat ρ
  let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  have honto : Function.Surjective f :=
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  let S := (T.subtype hM.1.2).mapSurjective (f := f) honto
  let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
  let := source_localAction_isSolvable hG T hempty hM
  let : K.Normal := Jhat_normal ρ
  have hf := imageRepresentation_injective M V (le_normalizer_conjugateSpanBy _ _)
  have hcore := source_localAction_twoCore hG T hM
  have hbound := source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ
  obtain ⟨hseed,hspan⟩ := source_localAction_seed_span hG T hM
  dsimp only
  by_cases hn : ∃ A ∈ QhatStar ρ, 1 < rank A
  · obtain ⟨A,hA,hr⟩ := hn
    obtain ⟨c,hfull,d,hd⟩ := source_centralizing_noncyclic_seed_factors
      hG T hempty hM hmany hJ A hA hr
    exact ⟨_,c,hfull,d,hd⟩
  have hrank : ∀ A ∈ QhatStar ρ, rank A = 1 := by
    intro A hA
    have hp := hA.1.2.1.rank_pos
    have hh : ¬1 < rank A := fun hh => hn ⟨A,hA,hh⟩
    omega
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hbound
  rcases QhatStar.ratio_one_or_two_of_rank_one ρ hf hA (hrank A hA) with hq | hq
  · obtain ⟨c,hfull,d,hd⟩ := source_localAction_ratioOne_factors hG T hempty hM hrank hq
    exact ⟨_,c,hfull,d,hd⟩
  have hKP : K ≤ (pCore 2 (D ⧸ fittingSubgroup D)).comap
      (QuotientGroup.mk' (fittingSubgroup D)) := by
    apply sSup_le
    intro B hB
    apply le_normalClosure.trans
    by_cases hm : ⁅pCore 5 D,B⁆ ≠ ⊥
    · exact CyclicSource.source_five_normalClosure_le_twoCore_preimage ρ hf hB (hrank B hB) hm
    · exact source_localAction_three_normalClosure hG T hempty hM hq hrank B hB (not_not.mp hm)
  have himage : IsPGroup 2 (K.map (QuotientGroup.mk' (fittingSubgroup D))) :=
    pCore_isPGroup.to_le (map_le_iff_le_comap.mpr hKP)
  let P := K ⊓ fittingSubgroup D
  let : P.Normal := inferInstanceAs (K ⊓ fittingSubgroup D).Normal
  have hodd : Odd (Nat.card P) := (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore).of_dvd_nat
    (Subgroup.card_dvd_of_le (show P ≤ fittingSubgroup D from inf_le_right))
  have hgen : K = P ⊔ (K ⊓ (S : Subgroup D)) :=
    eq_inf_sup_inf_sylow_of_quotient_image_isPGroup K (fittingSubgroup D) S himage
  let c := normalOddFactorData ρ hf K P S hodd hgen Z hseed hspan rfl ⟨A,hA⟩
  have hfull : subspaceCommutator c.representation ⊤ (fittingSubgroup K) = ⊤ := by
    rw [normalOddFactorData_representation ρ hf K P S hodd hgen Z hseed hspan rfl ⟨A,hA⟩]
    exact oddMovedAction_full_of_le ρ K P inf_le_left hodd _ (inf_fitting_subgroupOf_le K)
  exact ⟨_,c,hfull,source_fitting_decomposition c.representation c.faithful c.generated hfull
    (c.ratio ▸ hbound)⟩

/-- The first source paragraph of 15.1.2 with all movement and local
classification premises discharged on the original selected action. -/
theorem source_centralizing_classified_partition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∃ (U : Submodule (ZMod 2) (Additive (localModule T M))) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull ∧
      ∃ π : D →* Equiv.Perm d.Index,
        (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ Jhat ρ ≤ π.ker ∧ ∀ g i,
        Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
        (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor ∧
        (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  obtain ⟨U,c,_,d,hd⟩ := source_centralizing_factor_decomposition hG T hempty hM hmany hJ
  exact ⟨U,c,d,hd,source_localAction_classified_partition hG T hempty hM hmany hJ U c d hd⟩
end CFSG.Quasithin.Chapter15.Section01
