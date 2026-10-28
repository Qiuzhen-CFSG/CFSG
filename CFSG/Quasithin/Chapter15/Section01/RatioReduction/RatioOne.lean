module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.RatioOneReduction
public import CFSG.Quasithin.ChapterD.Section02.JhatRestriction
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NormalOddSeed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Assembly
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Seed
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SelectedAction
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The selected ratio-one action's literal factor family

The actual solvable image of M on V(M) has trivial two-core. In the cyclic
ratio-one case, its Jhat has a normal three-group two-residual. Intersecting
the marked Sylow with Jhat gives the odd-kernel factorization required by
the original fixed-seed theorem. The resulting action on the literal odd
support is faithful, fully Fitting-moved and preserves all original stars,
so D.2.16 supplies its finite indecomposable family.

Source: Aschbacher--Smith 15.1.2, first paragraph, printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter15.Section01
open Theory.GroupTheory Stellmacher ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
/-- The original ratio-one cyclic branch supplies the odd normal factorization
and its exact fully Fitting-moved factor datum from the original central seed. -/
theorem source_localAction_ratioOne_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let H := Jhat ρ
    let P := (pResidual 2 H).map H.subtype
    (∀ A ∈ QhatStar ρ, rank A = 1) → cubicRatio ρ = 1 →
    ∃ d : FactorData ρ H (subspaceCommutator ρ ⊤ P),
      subspaceCommutator d.representation ⊤ (fittingSubgroup H) = ⊤ ∧
        ∃ c : Decomposition d.representation, c.FittingFull := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let H := Jhat ρ
  let P := (pResidual 2 H).map H.subtype
  let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
  let := source_localAction_isSolvable hG T hempty hM
  let : H.Normal := Jhat_normal ρ
  let : P.Normal := inferInstanceAs ((pResidual 2 H).map H.subtype).Normal
  dsimp only
  intro hrank hq
  have hbound : cubicRatio ρ ≤ 2 := by rw [hq]; norm_num
  have hcore := cyclic_Jhat_core ρ (imageRepresentation_injective _ _ _)
    (source_localAction_twoCore hG T hM) hbound hrank
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hbound
  have hqH : cubicRatio (ρ.comp H.subtype) = 1 :=
    (subgroup_starred_transport ρ H ⟨A,hA,le_sSup hA⟩).1.trans hq
  have hp3 := hcore.ratioOne_residual_threeGroup (ρ.comp H.subtype) inferInstance hqH
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := (hp3.map H.subtype).exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  obtain ⟨S₀,hS₀⟩ := S.exists_subgroupOf_eq_of_normal H
  have hgen : H = P ⊔ (H ⊓ (S : Subgroup D)) := by
    have hh := congrArg (Subgroup.map H.subtype) (pResidual_sup_sylow_eq_top S₀)
    rw [Subgroup.map_sup,hS₀,subgroupOf_map_subtype,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    simpa only [inf_comm] using hh.symm
  have hPH : P ≤ H := map_subtype_le _
  have hPS : P.subgroupOf H = pResidual 2 H :=
    (Subgroup.map_injective H.subtype_injective) (map_subgroupOf_eq_of_le hPH)
  have hPF : P.subgroupOf H ≤ fittingSubgroup H := by
    rw [hPS]
    exact (show pResidual 2 H ≤ pCore 3 H from le_sSup ⟨inferInstance,hp3⟩).trans
      (pCore_le_fitting H 3)
  obtain ⟨hZ,hspan⟩ := source_localAction_seed_span hG T hM
  let d := normalOddFactorData ρ (imageRepresentation_injective _ _ _) H P S hodd hgen
    Z hZ hspan rfl ⟨A,hA⟩
  have hfull : subspaceCommutator d.representation ⊤ (fittingSubgroup H) = ⊤ := by
    rw [show d.representation = oddMovedAction ρ H P from
      normalOddFactorData_representation ρ (imageRepresentation_injective _ _ _) H P S hodd hgen
        Z hZ hspan rfl ⟨A,hA⟩]
    exact oddMovedAction_full_of_le ρ H P hPH hodd _ hPF
  exact ⟨d,hfull,source_fitting_decomposition d.representation d.faithful d.generated hfull
    (d.ratio ▸ hbound)⟩
end CFSG.Quasithin.Chapter15.Section01