module
public import CFSG.Quasithin.Chapter14.Section02.NormalMovement
public import CFSG.Quasithin.Chapter14.Section02.NormalBorelSource
public import CFSG.Quasithin.Chapter14.Section02.ResidualMovement
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source

/-!
# All six F.1.1 clauses for the original normal Bender branch

Keep K₁=K on the original ambient carrier, S=N_T(K₁)=T, and
S₂=O₂(Y)(T intersection K₁). The original common-normal theorem forces
Y=[Y,S₂], so YS₂ has quotient S₃ and its Borel is exactly S₂. The other
Borel is M intersection K₁ and normalizes YS₂. Both parabolics contain
the original Sylow and lie in actual characteristic-two locals. Together
with the proved generated-core calculation this establishes every F.1.1
clause. The original PSL₂, Suzuki, PSU₃ and SU₃ quotient models are retained;
no amalgam classification or unitary exclusion is assumed.

Source: Aschbacher--Smith 14.2.8(1), 14.2.11--15 and F.1.1,
printed pp.983--985 and 259.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem rankOne_model_equiv {A B : Type*} [Group A] [Group B]
    (e : B ≃* A) (h : ChapterF.Source.IsRankOneModel A) : ChapterF.Source.IsRankOneModel B := by
  cases h with
  | linear n hn h =>
    obtain ⟨F,hF,hfin,hcard,⟨d⟩⟩ := h
    exact .linear n hn ⟨F,hF,hfin,hcard,⟨e.trans d⟩⟩
  | suzuki m h => exact .suzuki m ⟨e.trans h.some⟩
  | projective_unitary n hn h =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨d⟩⟩ := h
    exact .projective_unitary n hn ⟨F,hF,hfin,J,hcard,hconj,⟨e.trans d⟩⟩
  | special_unitary n hn h =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨d⟩⟩ := h
    exact .special_unitary n hn ⟨F,hF,hfin,J,hcard,hconj,⟨e.trans d⟩⟩
  | dihedral h => exact .dihedral ⟨e.trans h.some⟩

theorem source_normal_bender_hypothesis_F_1_1
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (hres : pResidual 2 H = K)
    (hq : ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K)) :
    let Y := sourceResidual M Mc
    let K₁ := K.map H.subtype
    let S := (T : Subgroup G) ⊓ normalizer (K₁ : Set G)
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K₁)
    ChapterF.Source.HypothesisF11 ![K₁,Y ⊔ S₂] S ∧
      S = (T : Subgroup G) ∧ Y = ⁅Y,S₂⁆ ∧
      ChapterF.Source.borel K₁ S = M ⊓ K₁ ∧
      ChapterF.Source.borel (Y ⊔ S₂) S = S₂ := by
  let Y := sourceResidual M Mc
  let K₁ := K.map H.subtype
  let R := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K₁)
  let J := Y ⊔ R
  let S := (T : Subgroup G) ⊓ normalizer (K₁ : Set G)
  let B := ChapterF.Source.borel K₁ (T : Subgroup G)
  obtain ⟨hS,hQ,hR,hcore⟩ := source_normal_amalgam_core hG T hempty hM hu hmany hcard e H hH K hgen
  change S = (T : Subgroup G) at hS
  have hRT : R ≤ (T : Subgroup G) := hR.trans_eq hS
  have hQR : Y.pCoreIn 2 ≤ R := le_sup_left
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH K hgen hres hq
  obtain ⟨hmove,⟨eJ⟩⟩ := source_residual_actor_movement hG T hempty hM hu hmany hcard e R hRT hQR hnot
  obtain ⟨hinter,PJ,hPJ⟩ := source_residual_actor_sylow hG T hempty hM hu hmany hcard e R hRT hQR
  obtain ⟨hB,hcross⟩ := source_normal_borel_cross hG T hempty hM hu hmany hcard e H hH K hgen hq
  have hJM : J ≤ M := sup_le (sourceResidual_le _ _) (hRT.trans hM.1.2)
  have hJcard : Nat.card (J ⧸ pCore 2 J) = 6 :=
    (Nat.card_congr eJ.toEquiv).trans (by simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
  have hBJ : ChapterF.Source.borel J (T : Subgroup G) = R := by
    have hh := congrArg (Subgroup.map J.subtype)
      (sylow_normalizer_small_core_quotient PJ (Or.inl hJcard)).1
    have he := ChapterF.Source.borel_subgroupOf_eq_sylowNormalizer J (T : Subgroup G) PJ
      (hPJ.trans hinter.symm)
    change (ChapterF.Source.sylowNormalizer PJ).map J.subtype = (PJ : Subgroup J).map J.subtype at hh
    rw [←he,map_subgroupOf_eq_of_le (show ChapterF.Source.borel J (T : Subgroup G) ≤ J from inf_le_left),hPJ] at hh
    exact hh
  have hHN : H ≤ normalizer (K₁ : Set G) := by
    have hh := K.le_normalizer_map H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hTK : (T : Subgroup G) ≤ normalizer (K₁ : Set G) := hH.1.1.2.trans hHN
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    hM.1.2.trans ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le _ _)).mp (residualY_normal M Mc))
  have hTI : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ K₁ : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),le_normalizer_iff.mp hTK t ht x hx.2⟩
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (hTY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))) hTI).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (le_inf hTY hTR).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let TH := T.subtype hTH
  obtain ⟨PK,hPK⟩ := TH.exists_sylow_map_eq_inf_of_normal K
  have hsK : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ K₁) K₁ := by
    have hh := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr
      (show Chapter1.IsSylowIn 2 ((TH : Subgroup H) ⊓ K) K from ⟨PK,hPK⟩)
    simpa only [TH,Subgroup.map_inf _ _ _ H.subtype_injective,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH] using hh
  let a := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let aq := a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
    (IsPGroup.ker_isPGroup_of_injective a.injective)
  have hqK : ChapterF.Source.IsRankOneModel (K₁ ⧸ pCore 2 K₁) := rankOne_model_equiv aq hq
  have hqJ : ChapterF.Source.IsRankOneModel (J ⧸ pCore 2 J) :=
    (show SolvableAmalgam.SmallSolvableModel (J ⧸ pCore 2 J) from Or.inr (Or.inr ⟨eJ⟩)).rankOne
  have hKT : K₁ ⊔ (T : Subgroup G) = H := by
    change K ⊔ (T.subtype hTH : Subgroup H) = ⊤ at hgen
    have hh := congrArg (Subgroup.map H.subtype) hgen
    simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  let L : Fin 2 → Subgroup G := ![K₁,J]
  have hfit (A : Subgroup G) (hTA : (T : Subgroup G) ≤ A) (hAM : A ≤ M) :
      generalizedFitting A = pCore 2 A := by
    have hA := Chapter3.mem_HOver_of_sylow_interval T hTA hAM
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hA))
  have hF : ChapterF.Source.HypothesisF11 L (T : Subgroup G) := by
    refine ⟨inferInstance,T.isPGroup',?_,?_,?_,?_,?_,?_⟩
    · rw [Fin.forall_fin_two]
      constructor
      · exact hTK
      · exact hTJ
    · rw [Fin.forall_fin_two]
      constructor
      · exact hsK
      · exact ⟨PJ,hPJ.trans hinter.symm⟩
    · rw [Fin.forall_fin_two]
      constructor
      · exact hqK
      · exact hqJ
    · rw [Fin.forall_fin_two]
      constructor
      · change ChapterF.Source.borel J (T : Subgroup G) ≤ _
        rw [hBJ]
        exact hRT.trans hTK
      · exact hcross
    · change pCore 2 (ChapterF.Source.generated L S) = ⊥ at hcore
      change S = (T : Subgroup G) at hS
      rwa [hS] at hcore
    · rw [Fin.forall_fin_two]
      constructor
      · have he : ChapterF.Source.parabolic L (T : Subgroup G) 0 = H := by
          change K₁ ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel J (T : Subgroup G) = H
          rw [hBJ,hKT,sup_eq_left.mpr (hRT.trans hTH)]
        change generalizedFitting (ChapterF.Source.parabolic L (T : Subgroup G) 0) = _
        rw [he]
        exact generalizedFitting_eq_pCore_of_selfCentralizing 2
          (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1.1))
      · apply hfit
        · exact le_sup_right.trans le_sup_left
        · change J ⊔ (T : Subgroup G) ⊔ B ≤ M
          exact sup_le (sup_le hJM hM.1.2) (hB.le.trans inf_le_left)
  change ChapterF.Source.HypothesisF11 L S ∧ S = (T : Subgroup G) ∧ Y = ⁅Y,R⁆ ∧
    ChapterF.Source.borel K₁ S = M ⊓ K₁ ∧ ChapterF.Source.borel J S = R
  rw [hS]
  exact ⟨hF,rfl,hmove,hB,hBJ⟩
end CFSG.Quasithin.Chapter14.Section02
