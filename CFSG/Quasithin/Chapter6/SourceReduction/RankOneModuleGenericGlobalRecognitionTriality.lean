module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionTrialityModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionG2Short
public import Theory.SpecificGroups.Triality.ArmsLocalCoreCenter
public import Theory.SpecificGroups.Triality.ArmsParabolicPerfectAtTwo
public import Theory.SpecificGroups.Triality.ParabolicResiduals
public import Theory.SpecificGroups.Triality.BinaryLocalSections
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.Triality

/-!
# Triality orientation and local identification in the generic branch

The arms factor is the solvable residual of its full parabolic at every
positive binary exponent, including the perfect binary endpoint. Its
central core-center action excludes it as the original faithful left
factor. At the binary parameter the opposite parabolic is solvable,
so neither compatible orientation can occur for the prepared pair.

In the remaining orientation, restricting the actual parabolic
isomorphisms to solvable residuals identifies the left and right factors
with the genuine central and arms root factors. Comparison of the actual
PSL₂ quotient orders identifies the field exponent with the original n.
Transport gives the right quotient PSL₂(2^(3n)), left and right core
orders 2^(11n) and 2^(9n), and right core-center order 2^n.

For the diagram-selected right factor, the original two noncentral layers
contradict the arms degree/order bound. Hence both triality amalgam
orientations are excluded in that branch. The maps retain the whole
source overlap and S = O₂(N_G(L) ∩ H). The whole-residual branch, including
the U₅(4) alternative, remains in the Chapter12 consumer.

This is the local comparison in 5.2.6. Genuine amalgam classification,
the F.1.12 core bound and ambient completion recognition remain separate
obligations of qt-d-1222-rankone-generic-global. The original uniqueness
implication retains its independent producer.

Source: Aschbacher–Smith 5.2.6, printed pp.650–651; E.2.13(4), p.225;
F.1.12(I)(4), pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

namespace TrialityComparison

/-- The arms local factor is the full parabolic solvable residual, including q = 2. -/
theorem arms_parabolic_residual (P : Parameters) (hp : P.prime = 2) :
    (solvableResidual (parabolic P .arms)).map (parabolic P .arms).subtype =
      localFactor P .arms := by
  by_cases hq : 2 < P.q
  · exact parabolic_solvableResidual_map P hp hq .arms
  · have hq : P.q = 2 := by have := P.q_ge_two; omega
    let := parabolic_arms_isPerfect_at_two P hp hq
    rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype,
      parabolic_arms_eq_localFactor_at_two P hp hq]

end TrialityComparison

/-- The original faithful left factor cannot be the triality arms endpoint. -/
theorem Preparation.not_triality_arms_left_parabolic
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (P : Parameters) (hP : P.prime = 2) :
    ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) ≃*
      parabolic P .arms) := by
  rintro ⟨e⟩
  let X := ChapterF.Source.parabolic ![L,R] (sourceS L H) 0
  let Y := parabolic P .arms
  let a : solvableResidual X ≃* L :=
    ((solvableResidual X).equivMapOfInjective X.subtype X.subtype_injective).trans
      (MulEquiv.subgroupCongr (d.parabolic_residuals h hTH hp 0))
  let b : solvableResidual Y ≃* localFactor P .arms :=
    ((solvableResidual Y).equivMapOfInjective Y.subtype Y.subtype_injective).trans
      (MulEquiv.subgroupCongr (TrialityComparison.arms_parabolic_residual P hP))
  exact faithful_not_core_center_central h.local_mem.2
    (a.symm.trans (e.solvableResidualEquiv.trans b)) (arms_core_center_le_center P hP)

/-- The compatible orientation with the arms parabolic on the left is impossible. -/
theorem Preparation.not_triality_arms_left_amalgam
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (P : Parameters) (hP : P.prime = 2) :
    ¬ Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam P)) := by
  rintro ⟨e⟩
  exact d.not_triality_arms_left_parabolic h hTH hp P hP ⟨e.left⟩

/-- At q = 2 the central parabolic is solvable, excluding both orientations. -/
theorem Preparation.not_binary_triality_amalgams
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n) (hp : Group.IsPerfect R) :
    let α := sourceParabolicAmalgam ![L,R] (sourceS L H)
    let β := ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters 1 Nat.zero_lt_one)
    ¬ Nonempty (RankTwoAmalgam.Iso α β) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α β.reverse) := by
  let := _root_.Triality.Standard.BinaryLocalSections.central_parabolic_solvable
  constructor
  · rintro ⟨e⟩
    exact d.parabolics_not_solvable h hp 1
      (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)
  · rintro ⟨e⟩
    exact d.parabolics_not_solvable h hp 0
      (Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective)

/-- Every surviving triality amalgam has field exponent greater than one. -/
theorem Preparation.triality_parameter_gt_one
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n) (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    1 < m := by
  by_contra hm'
  have he : m = 1 := by omega
  subst m
  exact (d.not_binary_triality_amalgams h hp).2 ⟨e⟩


/-- Isomorphic binary PSL₂ groups have the same field order. This comparison
also fixes the original field in the linear and symplectic amalgam rows. -/
theorem binary_psl_field_card_eq
    {F E : Type*} [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2] (e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) : Nat.card F = Nat.card E := by
  let a := (Theory.PSL2.sl2QuotientEquiv F).trans
    (e.trans (Theory.PSL2.sl2QuotientEquiv E).symm)
  have he := Nat.card_congr a.toEquiv
  rw [GorensteinWalter.sl2_card_formula, GorensteinWalter.sl2_card_formula] at he
  have hf : 2 ≤ Nat.card F := Finite.one_lt_card
  have hg : 2 ≤ Nat.card E := Finite.one_lt_card
  have hmono : ∀ a b : ℕ, 2 ≤ a → a < b → a * (a^2-1) < b * (b^2-1) := by
    intro a b ha hab
    have hpos : 0 < a^2-1 := Nat.sub_pos_of_lt (by nlinarith)
    have hsq : a^2-1 ≤ b^2-1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hab.le 2) 1
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hab hpos) (Nat.mul_le_mul_left b hsq)
  rcases lt_trichotomy (Nat.card F) (Nat.card E) with h | h | h
  · exact (ne_of_lt (hmono _ _ hf h) he).elim
  · exact h
  · exact (ne_of_lt (hmono _ _ hg h) he.symm).elim

/-- Restriction of the original parabolic isomorphisms to their solvable
residuals identifies both selected factors with the genuine root factors. -/
theorem Preparation.triality_factor_equivs
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    Nonempty (L ≃* localFactor (binaryParameters m hm) .central) ∧
      Nonempty (R ≃* localFactor (binaryParameters m hm) .arms) := by
  have hgt := d.triality_parameter_gt_one h hp m hm e
  have hq : 2 < (binaryParameters m hm).q := by
    change 2^1 < 2^m
    exact Nat.pow_lt_pow_right (by decide) hgt
  let X := ChapterF.Source.parabolic ![L,R] (sourceS L H) 0
  let Y := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  let P := binaryParameters m hm
  let a : solvableResidual X ≃* L :=
    ((solvableResidual X).equivMapOfInjective X.subtype X.subtype_injective).trans
      (MulEquiv.subgroupCongr (d.parabolic_residuals h hTH hp 0))
  let b : solvableResidual (parabolic P .central) ≃* localFactor P .central :=
    ((solvableResidual (parabolic P .central)).equivMapOfInjective
      (parabolic P .central).subtype (parabolic P .central).subtype_injective).trans
        (MulEquiv.subgroupCongr (parabolic_solvableResidual_map P rfl hq .central))
  let c : solvableResidual Y ≃* R :=
    ((solvableResidual Y).equivMapOfInjective Y.subtype Y.subtype_injective).trans
      (MulEquiv.subgroupCongr (d.parabolic_residuals h hTH hp 1))
  let f : solvableResidual (parabolic P .arms) ≃* localFactor P .arms :=
    ((solvableResidual (parabolic P .arms)).equivMapOfInjective
      (parabolic P .arms).subtype (parabolic P .arms).subtype_injective).trans
        (MulEquiv.subgroupCongr (TrialityComparison.arms_parabolic_residual P rfl))
  exact ⟨⟨a.symm.trans (e.left.solvableResidualEquiv.trans b)⟩,
    ⟨c.symm.trans (e.right.solvableResidualEquiv.trans f)⟩⟩

/-- The field of the surviving orientation is the original left field.
No unrelated rank-two family tag or freely chosen field parameter is used. -/
theorem Preparation.triality_parameter_eq
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    m = n := by
  obtain ⟨⟨a⟩,_⟩ := d.triality_factor_equivs h hTH hp m hm e
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (localFactorCentralQuotientEquivPSL2 (binaryParameters m hm) rfl)
  obtain ⟨F,_,_,hF,⟨c⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hc := binary_psl_field_card_eq (c.symm.trans b)
  change Nat.card F = Nat.card (GaloisField 2 m) at hc
  rw [hF,GaloisField.card 2 m (by omega)] at hc
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hc).symm

/-- The surviving triality amalgam has its actual local quotients and core
orders at the original exponent. The special arms core center is transported
through the original right-factor isomorphism. -/
theorem Preparation.triality_local_structure
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    m = n ∧ 1 < m ∧
      Nonempty (L ≃* localFactor (binaryParameters m hm) .central) ∧
      Nonempty (R ≃* localFactor (binaryParameters m hm) .arms) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^(3*n)) ∧
      Nat.card (pCore 2 L) = (2^n)^11 ∧
      Nat.card (pCore 2 R) = (2^n)^9 ∧ Nat.card (center (pCore 2 R)) = 2^n := by
  have he := d.triality_parameter_eq h hTH hp m hm e
  obtain ⟨⟨a⟩,⟨b⟩⟩ := d.triality_factor_equivs h hTH hp m hm e
  let P := binaryParameters m hm
  let c := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
    (localFactorArmsQuotientEquivPSL2 P rfl)
  let aQ : pCore 2 L ≃* pCore 2 (localFactor P .central) :=
    (a.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 a))
  let bQ : pCore 2 R ≃* pCore 2 (localFactor P .arms) :=
    (b.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 b))
  refine ⟨he,d.triality_parameter_gt_one h hp m hm e,⟨a⟩,⟨b⟩,?_,?_,?_,?_⟩
  · refine ⟨ExtensionField P,inferInstance,inferInstance,?_,⟨c⟩⟩
    rw [card_extensionField,binaryParameters_q,he,←pow_mul,Nat.mul_comm n 3]
  · exact (Nat.card_congr aQ.toEquiv).trans
      (by simpa only [P,binaryParameters_q,he] using localFactor_central_twoCore_card P rfl)
  · exact (Nat.card_congr bQ.toEquiv).trans
      (by simpa only [P,binaryParameters_q,he] using localFactor_arms_twoCore_card P rfl)
  · exact (Nat.card_congr (centerCongr bQ).toEquiv).trans
      (by simpa only [P,binaryParameters_q,he] using localFactor_arms_twoCore_center_card P rfl)


/-- In the surviving orientation the right factor is the actual arms residual.
Its two original noncentral layers violate the degree/order bound. -/
theorem Preparation.not_triality_arms_right_amalgam
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (m : ℕ) (hm : 0 < m) :
    ¬ Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) := by
  rintro ⟨e⟩
  let := hp
  obtain ⟨_,⟨a⟩⟩ := d.triality_factor_equivs h hTH hp m hm e
  exact TrialityComparison.arms_no_two_layers hl m hm a

/-- Both compatible triality orientations are excluded for the selected diagram
factor. All maps retain the whole original overlap, including both odd Cartans. -/
theorem Preparation.not_triality_amalgams
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (m : ℕ) (hm : 0 < m) :
    let α := sourceParabolicAmalgam ![L,R] (sourceS L H)
    let β := ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)
    ¬ Nonempty (RankTwoAmalgam.Iso α β) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α β.reverse) :=
  ⟨d.not_triality_arms_left_amalgam h hTH hp _ rfl,
    d.not_triality_arms_right_amalgam h hTH hp hl m hm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
