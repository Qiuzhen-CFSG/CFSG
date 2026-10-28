module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOddSubgroupTerminal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOverlap

/-!
# The odd rank-one subgroup escapes the original maximal overlap

If the selected rank-one subgroup lay in M, its inclusion in M₁ would make
it normalize the original solvable quintic residual. The residual's image
in the actual simple PSL₂ quotient would be a solvable normal subgroup,
hence trivial. This would make the original residual a two-group despite
its quotient of order five. Thus the subgroup lies outside M, and the
original full-kernel fusion terminal applies.

Source: Aschbacher--Smith6.1.4, the replacement of K₁ by K₂ on printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original comparison subgroup needs only actual containment of X,
T-invariance and its PSL₂ two-core quotient. Escape from M is proved here. -/
theorem original_hermitian_no_odd_linear_comparison_subgroup
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hKM₁ : K ≤ M₁) (hXK : quinticResidual T L ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (p d : ℕ) (hp : p.Prime) (ho : Odd p) (hd : d = 1 ∨ d = 2)
    (hlarge : 3 < p^d) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p^d) := by
  intro hmodel
  have hnot : ¬ K ≤ M := by
    intro hKM
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
    let Q := K ⧸ pCore 2 K
    let : IsSimpleGroup PSL(2,F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF]; omega)
    let : Group.IsPerfect PSL(2,F) := GorensteinWalter.psl2_isPerfect_of_card_gt_three F
      (by rw [hF]; exact hlarge)
    let : IsSimpleGroup Q := e.isSimpleGroup
    let : Group.IsPerfect Q :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    let X := quinticResidual T L
    let R := X.subgroupOf K
    let er : R ≃* X := subgroupOfEquivOfLe hXK
    let q := QuotientGroup.mk' (pCore 2 K)
    have hi := h.rankOneInput hout
    let : Group.IsSolvable (localBorel T L) :=
      localBorel_isSolvable hi.exponent hi.linear hi.sylow_normalizes
    let : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (show X ≤ localBorel T L from map_subtype_le _))
    let : Group.IsSolvable R :=
      Group.isSolvable_of_isSolvable_injective (f := er.toMonoidHom) er.injective
    let : R.Normal := normal_subgroupOf_of_le_normalizer
      ((le_inf hKM hKM₁).trans (original_hermitian_quintic_overlap h hout hm hM₁ hCM₁).2)
    let Y := R.map q
    let : Y.Normal := (inferInstance : R.Normal).map q (QuotientGroup.mk'_surjective _)
    let : Group.IsSolvable Y := Group.isSolvable_of_surjective (q.subgroupMap_surjective R)
    have hY : Y = ⊥ := by
      rcases (inferInstance : Y.Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · have hs : Group.IsSolvable (⊤ : Subgroup Q) := ht ▸ inferInstance
        let := hs
        exact (Group.IsPerfect.not_isSolvable Q
          (Group.isSolvable_of_surjective (f := (topEquiv (G := Q)).toMonoidHom)
            (topEquiv (G := Q)).surjective)).elim
    have hR : R ≤ pCore 2 K := by
      have hh := (map_eq_bot_iff R).mp hY
      simpa only [q,QuotientGroup.ker_mk'] using hh
    have hXtwo : IsPGroup 2 X := (pCore_isPGroup.to_le hR).of_equiv er
    have hQtwo : IsPGroup 2 (X ⧸ pCore 2 X) := hXtwo.of_surjective
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hc := hQtwo.card_eq_or_dvd
    rw [(original_hermitian_quintic_core_quotient h hout hm).2] at hc
    norm_num at hc
  exact original_hermitian_no_odd_linear_subgroup h hout hm hXK hTK hnot
    p d hp ho hd hlarge hmodel

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
