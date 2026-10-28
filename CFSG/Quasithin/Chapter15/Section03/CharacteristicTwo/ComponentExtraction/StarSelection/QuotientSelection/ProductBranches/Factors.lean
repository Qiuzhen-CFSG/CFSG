module

public import Theory.GroupTheory.PResidual.SylowSupplement
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents.FactorModels

/-!
# Structure of the B.5.6 direct factors

Each factor is S₃, or has a quasisimple solvable residual of index at most
two and no nontrivial normal solvable subgroup. Simplicity of the actual
projective linear groups and the alternating subgroup of S₅ supply these
facts. The index bound gives generation by the residual and any Sylow
two-subgroup. These facts apply to all action cases of B.5.6(3),(5).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6,
printed p.105, and the selection in 15.3.15(2)/26(2), pp.1125 and 1130.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection.ProductBranches
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
private theorem model_cases (h : FactorModel D) :
    Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨ IsSimpleGroup D ∨
      Nonempty (D ≃* Equiv.Perm (Fin 5)) := by
  cases h with
  | linearTwo F e =>
    by_cases hn : F.degree = 1
    · have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq, hn]; rfl
      let := Fintype.ofFinite F.Carrier
      let f : F.Carrier ≃+* ZMod 2 :=
        (ZMod.ringEquivOfPrime F.Carrier (by decide)
          (by simpa only [← Nat.card_eq_fintype_card] using hc)).symm
      obtain ⟨g⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
      exact Or.inl ⟨e.trans ((Atlas.fieldEquivSL 2 f).trans g)⟩
    · have hc : 4 ≤ Nat.card F.Carrier := by
        rw [F.card_eq]
        have hd := F.degree_pos
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ F.degree)
      let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F.Carrier) hc
      exact Or.inr (Or.inl ((e.trans (sl2Projective F)).isSimpleGroup_congr.mpr inferInstance))
  | symmetricFive e => exact Or.inr (Or.inr ⟨e⟩)
  | linearThree F ho e =>
    let := Atlas.psl_simple_high_rank (F := F.Carrier) 3 (by decide)
    exact Or.inr (Or.inl ((e.trans (sl3Projective F ho)).isSimpleGroup_congr.mpr inferInstance))

omit [Finite D] in
private theorem residual_ne_bot (hq : IsQuasisimple (solvableResidual D)) :
    solvableResidual D ≠ ⊥ := by
  let := hq
  let := hq.simple
  let : Nontrivial (solvableResidual D) :=
    (QuotientGroup.mk'_surjective (center (solvableResidual D))).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance

private theorem a5_perfect : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  ⟨commutator_alternatingGroup_eq_top (by simp)⟩

/-- A nonsolvable source factor has no nontrivial normal solvable subgroup,
and its solvable residual has index at most two. -/
theorem factor_structure (h : FactorModel D) :
    Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨
      (IsQuasisimple (solvableResidual D) ∧ (solvableResidual D).index ≤ 2 ∧
        ∀ K : Subgroup D, K.Normal → Group.IsSolvable K → K = ⊥) := by
  rcases factor_residual h with ⟨he, _⟩ | ⟨hq, _⟩
  · exact Or.inl he
  rcases model_cases h with he | hr
  · exact Or.inl he
  rcases hr with hs | he
  · right
    let := hs
    have hr : solvableResidual D = ⊤ :=
      (inferInstance : (solvableResidual D).Normal).eq_bot_or_eq_top.resolve_left
        (residual_ne_bot hq)
    let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
      (f := ((MulEquiv.subgroupCongr hr).trans topEquiv).toMonoidHom)
      ((MulEquiv.subgroupCongr hr).trans topEquiv).surjective
    refine ⟨hq, by rw [hr]; simp, ?_⟩
    intro K hn hk
    let := hn
    let := hk
    rcases hn.eq_bot_or_eq_top with hb | ht
    · exact hb
    · let : Group.IsSolvable D := Group.isSolvable_of_surjective
        (f := ((MulEquiv.subgroupCongr ht).trans topEquiv).toMonoidHom)
        ((MulEquiv.subgroupCongr ht).trans topEquiv).surjective
      exact (Group.IsPerfect.not_isSolvable D inferInstance).elim
  · right
    obtain ⟨e⟩ := he
    let := a5_perfect
    have hr : (solvableResidual D).index ≤ 2 := by
      rw [← index_map_equiv _ e, map_solvableResidual_eq _ e.surjective]
      exact (index_antitone (le_solvableResidual_of_isPerfect (alternatingGroup (Fin 5)))).trans_eq
        alternatingGroup.index_eq_two
    refine ⟨hq, hr, ?_⟩
    intro K hn hk
    let := hn
    let := hk
    let K' := K.map e.toMonoidHom
    let : K'.Normal := hn.map _ e.surjective
    let : Group.IsSolvable K' := Group.isSolvable_of_surjective
      (e.toMonoidHom.subgroupMap_surjective K)
    have hb : K' = ⊥ := by
      by_contra hne
      let : Nontrivial K' := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      have ha := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 5))
        (inferInstance : Nontrivial K')
      let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
        Group.isSolvable_of_isSolvable_injective (inclusion_injective ha)
      exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance
    exact (map_eq_bot_iff_of_injective K e.injective).mp hb

/-- An index-one or index-two residual is supplemented by every Sylow two-subgroup. -/
theorem residual_sup_sylow_of_index (P : Sylow 2 D)
    (hi : (solvableResidual D).index ≤ 2) :
    solvableResidual D ⊔ (P : Subgroup D) = ⊤ := by
  have hp : IsPGroup 2 (D ⧸ solvableResidual D) := by
    have hn := (solvableResidual D).index_ne_zero_of_finite
    have he : (solvableResidual D).index = 1 ∨ (solvableResidual D).index = 2 := by omega
    rcases he with he | he
    · exact IsPGroup.of_card (n := 0) (by simpa only [← index_eq_card, pow_zero] using he)
    · exact IsPGroup.of_card (n := 1) (by simpa only [← index_eq_card, pow_one] using he)
  have hr : pResidual 2 D ≤ solvableResidual D := sInf_le ⟨inferInstance, hp⟩
  exact top_unique ((pResidual_sup_sylow_eq_top P).symm.le.trans (sup_le_sup_right hr _))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection.ProductBranches
