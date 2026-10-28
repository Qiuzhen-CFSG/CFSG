module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsCoreProduct

/-!
# The original Hermitian centralizer has index sixteen in the Tits core

The full inner Sylow quotient of LT has order sixteen. The proved identity
R Q = S, with R = O₂(KT) and Q = O₂(LT), identifies the original core
centralizer C_R(B) with R ∩ Q and gives its exact index. This supplies a
fixed-index bound on the literal Frattini quotient of R without discarding
any part of either core.

Source application: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The entire original inner Sylow has quotient of order sixteen by the
entire original LT core, under the original Hermitian marking. -/
theorem original_hermitian_inner_sylow_core_index
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2)) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex
      (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) = 16 := by
  let J := L ⊔ (T : Subgroup G)
  let C := L.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let hi := h.reduced_enlargement.rankOneInput hout
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer hi.sylow_normalizes)
  let N := C.map q
  let : N.Normal := (inferInstance : C.Normal).map q hq
  let ec : C ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let eqc := QuotientGroup.congr (pCore 2 C) (pCore 2 L) ec (pCore_map_iso 2 ec)
  let eN : N ≃* (L ⧸ pCore 2 L) := (coreQuotientEquivImage 2 C).symm.trans eqc
  obtain ⟨eL,f,hf⟩ := hm
  let en := eN.trans eL
  let Pq := P.mapSurjective hq
  let S := ((T : Subgroup G) ⊓ L) ⊔ J.pCoreIn 2
  have hUJ : (T : Subgroup G) ⊓ L ≤ J := inf_le_left.trans le_sup_right
  have hQJ : J.pCoreIn 2 ≤ J := pCoreIn_le 2 J
  have hSJ : S ≤ J := sup_le hUJ hQJ
  have hQsub : (J.pCoreIn 2).subgroupOf J = pCore 2 J := by
    change ((pCore 2 J).map J.subtype).comap J.subtype = pCore 2 J
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hSimage : (S.subgroupOf J).map q = (Pq : Subgroup _) ⊓ N := by
    have hkerP : q.ker ≤ (P : Subgroup J) := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal P
    have hUq : ((P : Subgroup J) ⊓ C).map q = (Pq : Subgroup _) ⊓ N := by
      rw [inf_comm,map_inf_of_ker_le q C (P : Subgroup J) hkerP,inf_comm]
      rfl
    have hmapQ : (pCore 2 J).map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
    rw [show S = ((T : Subgroup G) ⊓ L) ⊔ J.pCoreIn 2 from rfl,
      subgroupOf_sup hUJ hQJ,Subgroup.map_sup,hQsub,hmapQ,sup_bot_eq]
    exact hUq
  obtain ⟨U,hU⟩ := Pq.exists_subgroupOf_eq_of_normal N
  let U' := U.mapSurjective (f := en.toMonoidHom) en.surjective
  have hUc : Nat.card U = 16 := by
    have hc : Nat.card U' = 16 :=
      (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive
        (OrthogonalFourMinus.FiniteModel.Field 2) 2 U').symm.toEquiv).trans
        ((GaloisField.card 2 4 (by decide)).trans (by norm_num))
    change Nat.card ((U : Subgroup N).map en.toMonoidHom) = 16 at hc
    rwa [card_map_of_injective en.injective] at hc
  have hNcard : Nat.card ((Pq : Subgroup _) ⊓ N : Subgroup (J ⧸ pCore 2 J)) = 16 := by
    have hc : Nat.card ((U : Subgroup N).map N.subtype) = 16 := by
      rw [card_map_of_injective N.subtype_injective]
      exact hUc
    rw [hU,subgroupOf_map_subtype] at hc
    simpa only [inf_comm] using hc
  have hidx : (pCore 2 J).relIndex (S.subgroupOf J) = 16 := by
    rw [←QuotientGroup.ker_mk' (pCore 2 J),relIndex_ker,hSimage]
    exact hNcard
  have hh := relIndex_map_map_of_injective (pCore 2 J) (S.subgroupOf J) J.subtype_injective
  rw [map_subgroupOf_eq_of_le hSJ] at hh
  exact hh.trans hidx

/-- The centralizer of the whole original module in the whole Tits core
is its intersection with the original LT core, of exact index sixteen. -/
theorem original_hermitian_tits_core_module_centralizer_index
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    let R := (K ⊔ (T : Subgroup G)).pCoreIn 2
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    let B := reducedSubgroup (L ⊔ (T : Subgroup G))
    R ⊓ centralizer (B : Set G) = R ⊓ Q ∧
      (centralizer (B : Set G)).relIndex R = 16 := by
  let R := (K ⊔ (T : Subgroup G)).pCoreIn 2
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  have hRT : R ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hC : (T : Subgroup G) ⊓ centralizer (B : Set G) = Q :=
    full_reduced_hermitian_sylow_centralizer h hm
  have heq : R ⊓ centralizer (B : Set G) = R ⊓ Q := by
    rw [←hC,←inf_assoc,inf_eq_left.mpr hRT]
  have hRQ : R ≤ normalizer (Q : Set G) :=
    hRT.trans (le_sup_right.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))))
  have hidx : Q.relIndex R = 16 := by
    let A := R ⊔ Q
    let : (Q.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le hRQ Q.le_normalizer)
    have hs := relIndex_sup_right (R.subgroupOf A) (Q.subgroupOf A)
    rw [←subgroupOf_sup le_sup_left le_sup_right,
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf le_sup_left] at hs
    calc
      Q.relIndex R = Q.relIndex (R ⊔ Q) := hs.symm
      _ = Q.relIndex (((T : Subgroup G) ⊓ L) ⊔ Q) := by
        rw [original_hermitian_tits_core_sup_original_core h hout hm hM₁ hCM₁ hK hnot hqK e]
      _ = 16 := original_hermitian_inner_sylow_core_index h hout hm
  refine ⟨heq,?_⟩
  calc
    (centralizer (B : Set G)).relIndex R =
        (centralizer (B : Set G) ⊓ R).relIndex R :=
      (inf_relIndex_right _ _).symm
    _ = (R ⊓ centralizer (B : Set G)).relIndex R := by rw [inf_comm]
    _ = (R ⊓ Q).relIndex R := congrArg (fun Z => Z.relIndex R) heq
    _ = Q.relIndex R := inf_relIndex_left _ _
    _ = 16 := hidx

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
