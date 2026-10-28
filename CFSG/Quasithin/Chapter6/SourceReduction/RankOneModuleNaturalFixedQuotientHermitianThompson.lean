module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuintic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientCubic
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# The original Thompson subgroup in the full Hermitian case

The faithful original LT/O₂(LT) action on a whole Hermitian module of
half-degree greater than one is not an FF-module. Thus the maximum
elementary subgroups of the original Sylow centralize that module and
lie in O₂(LT). The intermediate-subgroup identity gives J(T)=J(O₂(LT)).
Consequently LT, and in particular the actual quintic product XT,
normalizes J(T). No stationary Thompson premise or chosen quotient is
assumed. The later outside-component fusion argument remains separate.

Source: Aschbacher--Smith, Remark 6.1.2 and 6.1.4, printed pp.663,665--666.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source
namespace RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n s : ℕ} [NeZero s]

/-- A full original Hermitian module forces the actual Thompson subgroup
to be the Thompson subgroup of the literal local two-core. -/
theorem Input.hermitian_thompson_eq_twoCore
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsConjugationModel L W (SL2.BinarySmall.hermitian s)) (hs : 1 < s) :
    elementaryAbelianMaxJ (T : Subgroup G) =
      elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let J := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf J
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (U : Set J) :=
    (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_eq_twoCore.symm
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hno : ¬ IsFFModule ρ := by
    obtain ⟨hsource,⟨M⟩⟩ := h.hermitian_original_source hm
    rcases (hsource.orthogonal_case M).2 with hn | ⟨hs1,_⟩
    · exact hn.2.2.2
    · omega
  have hJS : elementaryAbelianMaxJ (S : Subgroup J) ≤ pCore 2 J := by
    by_contra hn
    apply hno
    apply NormalElementaryQuotient.isFFModule_of_thompson_not_le U q hq hk
      (S : Subgroup J) (comap_mono h.reduced_le_sylow)
    simpa only [q,QuotientGroup.ker_mk'] using hn
  have hSm : (S : Subgroup J).map J.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ J.pCoreIn 2 := by
    have hh := map_mono (f := J.subtype) hJS
    rwa [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,hSm] at hh
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow J S).trans_eq hSm
  exact (elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) _ hJQ hQT).symm

/-- The whole original local group preserves the Thompson subgroup in
the full Hermitian case. -/
theorem Input.hermitian_join_normalizes_thompson
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsConjugationModel L W (SL2.BinarySmall.hermitian s)) (hs : 1 < s) :
    L ⊔ (T : Subgroup G) ≤ normalizer
      (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  rw [h.hermitian_thompson_eq_twoCore hm hs]
  exact ((L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _
      (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))) |>.trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _)

end RankOneGeneric
namespace RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- Remark 6.1.2 on the actual full reduced subgroup in the remaining
Hermitian degree-four source configuration. -/
theorem original_hermitian_four_thompson_eq_twoCore
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2)) :
    elementaryAbelianMaxJ (T : Subgroup G) =
      elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) :=
  (h.reduced_enlargement.rankOneInput hout).hermitian_thompson_eq_twoCore hm (by decide)

/-- The literal X=O^{5′}(N_L(T∩L)) and the original Sylow preserve J(T),
as required before the source's final elementary-subgroup fusion. -/
theorem original_hermitian_quintic_normalizes_thompson
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2)) :
    quinticResidual T L ⊔ (T : Subgroup G) ≤ normalizer
      (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  apply le_trans ?_
    ((h.reduced_enlargement.rankOneInput hout).hermitian_join_normalizes_thompson hm (by decide))
  exact sup_le_sup_right ((map_subtype_le _).trans inf_le_left) _

end RankOneRecognition
end CFSG.Quasithin.Chapter6.Source
