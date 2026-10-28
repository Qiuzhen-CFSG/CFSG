module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHermitianThompsonControl
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticSylowCore

/-!
# The original maximum elementary witness before fusion

An outside subgroup K cannot normalize J(T). If J(T) lay in O₂(KT),
Thompson heredity would make it characteristic there and normalized by K.
Hence a genuine maximum elementary subgroup of T has nontrivial image in
KT/O₂(KT). The Hermitian Thompson identity puts this same subgroup inside
the actual O₂(XT).
Source: the final paragraph of Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V K : Subgroup G} {n : ℕ}

/-- The actual maximum elementary family supplies a nontrivial quotient
witness lying in O₂(XT), with no fusion or image premise. -/
theorem original_hermitian_outside_maximum_elementary_witness
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2)) (hK : ¬ K ≤ M) :
    ∃ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
      A ≤ (quinticResidual T L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ A ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let R := (K ⊔ (T : Subgroup G)).pCoreIn 2
  have hRT : R ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hJR : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ R := by
    intro hj
    apply original_hermitian_outside_not_normalizes_thompson h hout hm hK
    rw [←elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) R hj hRT]
    exact (le_sup_left.trans ((K ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G))))).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ R)
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), ¬ A ≤ R := by
    by_contra! hh
    exact hJR (sSup_le hh)
  obtain ⟨A,hA,hAR⟩ := hex
  refine ⟨A,hA,?_,hAR⟩
  have hAJ : A ≤ elementaryAbelianMaxJ (T : Subgroup G) := le_sSup hA
  rw [original_hermitian_quintic_sylow_core h hout hm]
  apply hAJ.trans
  rw [original_hermitian_four_thompson_eq_twoCore h hout hm]
  exact (sSup_le fun _ hb => hb.1).trans le_sup_right

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
