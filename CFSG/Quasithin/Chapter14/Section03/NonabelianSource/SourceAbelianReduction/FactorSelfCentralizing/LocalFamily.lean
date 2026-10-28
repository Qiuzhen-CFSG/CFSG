module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.CoreComponent
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.DeletedPointComponent
public import Theory.GroupTheory.FourGroupTwoGroupAction
public import Theory.GroupTheory.SpecificGroups.DihedralEightProductElementary
public import Theory.ElementaryAbelian.Injective

/-!
# Local-family placement of the marked A₅ block

The marked point centralizer is perfect by irreducibility of its translation
kernel and perfectness of its A₅ quotient. It is normal in the join with the
original RQ-centralizer. For the Sylow clause, RQ normalizes the elementary
four-group C_G(A) ∩ D. Its action has order at most two, so C_RQ(d) has at
least 256 elements. The literal marked normalizer centralizer has order
3840, proving Sylow membership. The normal sixteen-group A supplies the
nontrivial two-core in the join.

Source: Aschbacher--Smith, 14.3.20, pp.997--998; Definition 1.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition BinaryPermutation.SixNaturalSplit
variable {G : Type*} [Group G] [Finite G]

theorem localFamilySource_of_source_hypotheses
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot) :
    LocalFamilySource F (sourceResidual M Mc) := by
  intro A hA hlt P z hz _hgeom _hSylow
  let := hA.elementary
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q := F.H.pCoreIn 2
  let W := R ⊔ Q
  let K := factorBlock F (sourceResidual M Mc) A
  let N := normalizer (A : Set G)
  let C := centralizer (A : Set G)
  let D := Q ⊓ centralizer (F.U : Set G)
  let E := C ⊓ D
  let X := N ⊓ P.globalCentralizer
  let B := P.blockCentralizer
  let S := P.localSylow
  let J := B ⊔ S
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg, he, _, _, _, _, _⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hWN : W ≤ N := (sup_le_sup (pCoreIn_le 2 _) le_rfl).trans hA.normalized
  obtain ⟨_, _, PN, hPN⟩ := factor_normalizer_sylow_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized
  change (PN : Subgroup N).map N.subtype = W at hPN
  have hWp : IsPGroup 2 W := hPN ▸ PN.isPGroup'.map N.subtype
  have hNcard : Nat.card N = 23040 := (source_factor_full_automorphism_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    A hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized hlt).2.1
  have hWcard : Nat.card W = 512 := by
    rw [← hPN, card_map_of_injective N.subtype_injective, PN.card_eq_multiplicity, hNcard]
    rw [show 23040 = 2 ^ 9 * 45 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
    norm_num
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hRT : R ≤ (T : Subgroup G) := (source_parabolic_core_sylow_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow F.H (T.subtype hTH)
  have hWH : W ≤ F.H := (sup_le hRT hQT).trans hTH
  have hHD : F.H ≤ normalizer (D : Set G) :=
    (le_inf (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
      ((le_normalizer_conjugateSpanBy _ _).trans
        (normalizer_le_normalizer_centralizer F.U))).trans inf_normalizer_le_normalizer_inf
  have hWE : W ≤ normalizer (E : Set G) :=
    (le_inf (hWN.trans (normalizer_le_normalizer_centralizer A))
      (hWH.trans hHD)).trans inf_normalizer_le_normalizer_inf
  have hEC := (source_factor_centralizer_elementary_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    A hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized).1
  let := hEC
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (inclusion (show E ≤ C from inf_le_left)) (inclusion_injective _)
  have hzmem : z ∈ F.Vi 1 := hz.symm ▸ mem_zpowers z
  have hzA : z ∈ A := hA.seed_le (F.le_seed 1 hzmem)
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← hz]
    simpa using F.card 1 (by decide)
  have hzU : z ∈ F.ZU := hZ.symm ▸ hzmem
  have hUQ : F.U ≤ Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hzD : z ∈ D :=
    ⟨hUQ (map_subtype_le (center F.U) hzU), centerIn_le_centralizer F.U hzU⟩
  have hzE : z ∈ E := ⟨hlt.le hzA, hzD⟩
  have hdE : P.element ∈ E := ⟨P.centralizes_factor, P.mem_supplement⟩
  have hEFour : Nat.card E = 4 := by
    have hzd : zpowers z ≤ A := zpowers_le.mpr hzA
    have hdout : P.element ∉ zpowers z := fun hd => P.outside_factor (hzd hd)
    have hdn : P.element ∈ normalizer (zpowers z : Set G) :=
      _root_.centralizer_le_normalizer _ ((centralizer_le hzd) P.centralizes_factor)
    have hc : Nat.card (zpowers z ⊔ zpowers P.element : Subgroup G) = 4 := by
      rw [card_sup_zpowers_of_normalizing_involution _ _
        (by rw [← P.point_order]; exact pow_orderOf_eq_one _) hdout hdn,
        Nat.card_zpowers, hz2]
    have hlo : 4 ≤ Nat.card E := hc ▸ card_le_of_le
      (sup_le (zpowers_le.mpr hzE) (zpowers_le.mpr hdE))
    obtain ⟨eD⟩ := source_factor_supplement_dihedral_of_strict_centralizer
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
      A hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized hlt
    let : IsElementaryAbelian 2 (E.subgroupOf D) := IsElementaryAbelian.subgroupOf inf_le_right
    let : IsElementaryAbelian 2 ((E.subgroupOf D).map eD.toMonoidHom) :=
      IsElementaryAbelian.map eD.toMonoidHom
    have hhi := DihedralGroup.elementary_card_le_four
      ((E.subgroupOf D).map eD.toMonoidHom) inferInstance
    rw [card_map_of_injective eD.injective,
      Nat.card_congr (subgroupOfEquivOfLe (show E ≤ D from inf_le_right)).toEquiv] at hhi
    exact le_antisymm hhi hlo
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hEFour]; decide)
  let : IsKleinFour E := ⟨hEFour, IsElementaryAbelian.exponent_eq_prime⟩
  let a := E.normalizerMonoidHom.comp (inclusion hWE)
  have hker : a.ker = (centralizer (E : Set G)).subgroupOf W := by
    ext w
    change E.normalizerMonoidHom (inclusion hWE w) = 1 ↔ _
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    rfl
  have hi : (centralizer (E : Set G)).relIndex W ≤ 2 := by
    change ((centralizer (E : Set G)).subgroupOf W).index ≤ 2
    rw [← hker, index_ker]
    exact four_twoGroup_action_card E W hWp hWE
  have hiS : S.relIndex W ≤ 2 := by
    change (W ⊓ P.globalCentralizer).relIndex W ≤ 2
    rw [inf_relIndex_left]
    exact (relIndex_le_of_le_left
      (centralizer_le (Set.singleton_subset_iff.mpr hdE))
      ((centralizer (E : Set G)).subgroupOf W).index_ne_zero_of_finite).trans hi
  have hScard : 256 ≤ Nat.card S := by
    have hh := relIndex_mul_card_of_le (show S ≤ W from inf_le_left)
    rw [hWcard] at hh
    nlinarith
  have hSp : IsPGroup 2 S := hWp.to_le inf_le_left
  have hSX : S ≤ X := inf_le_inf_right _ hWN
  have hnorm : N = normalizer (K : Set G) := (source_factor_block_normalizer_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    A hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized).2
  have hb := (source_factor_full_automorphism_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    A hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized hlt).1
  have hXcard : Nat.card X = 3840 := by
    change Nat.card (N ⊓ P.globalCentralizer : Subgroup G) = _
    rw [hnorm]
    exact pointNormalizerCentralizer_card K P.marking P.point P.point_action
      natural_block_normalizer hb
  have hSylX : Chapter1.IsSylowIn 2 S X := by
    obtain ⟨PX, hPX⟩ := (hSp.comap_subtype : IsPGroup 2 (S.subgroupOf X)).exists_le_sylow
    have hPXcard : Nat.card PX = 256 := by
      rw [PX.card_eq_multiplicity, hXcard]
      rw [show 3840 = 2 ^ 8 * 15 by decide,
        Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
      norm_num
    have hScard' : 256 ≤ Nat.card (S.subgroupOf X) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hSX).toEquiv]
      exact hScard
    have heq : S.subgroupOf X = (PX : Subgroup X) :=
      eq_of_le_of_card_ge hPX (hPXcard.le.trans hScard')
    refine ⟨PX, ?_⟩
    rw [← heq, map_subgroupOf_eq_of_le hSX]
  have hBX : B ≤ X := le_inf P.blockCentralizer_normalizes_factor inf_le_right
  have hJX : J ≤ X := sup_le hBX hSX
  have hJB : J ≤ normalizer (B : Set G) := by
    have hXK : X ≤ normalizer (K : Set G) := inf_le_left.trans hnorm.le
    exact hJX.trans ((le_inf hXK (inf_le_right.trans P.globalCentralizer.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf)
  have hBJ : B ≤ J := le_sup_left
  let hnB : (B.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJB
  have ht : (⊤ : Subgroup B).IsCComponent := pointBlock_isCComponent_top
    K A hA.card P.marking P.factor_map P.factor_le P.point P.point_action
    P.factor_le_blockCentralizer
  have ht' : (⊤ : Subgroup (B.subgroupOf J)).IsCComponent := by
    have hh := ht.map_equiv (subgroupOfEquivOfLe hBJ).symm
    rwa [map_top_of_surjective _ (subgroupOfEquivOfLe hBJ).symm.surjective] at hh
  have hcomp : (B.subgroupOf J).IsCComponent := by
    have hh := ht'.map_subtype hnB.isSubnormal
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hAJ : A ≤ J := P.factor_le_blockCentralizer.trans hBJ
  have hJA : J ≤ normalizer (A : Set G) := hJX.trans inf_le_left
  have hcore : A ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes hA.elementary.isPGroup hAJ hJA
  refine ⟨hcomp, hSylX.restrict le_sup_right hJX, ?_⟩
  intro heq
  have ha0 : A = ⊥ := le_bot_iff.mp (hcore.trans_eq heq)
  have hc1 : Nat.card A = 1 := card_eq_one.mpr ha0
  have hc16 := hA.card
  omega

/-- The local-family premise of the original core-component assembly is
discharged. Only the independent residual-commutator source remains. -/
theorem coreComponentSource_of_commutator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hcomm : ResidualCommutatorSource F (sourceResidual M Mc)) :
    CoreComponentSource F (sourceResidual M Mc) := by
  exact coreComponentSource_of_localFamily_and_commutator
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    (localFamilySource_of_source_hypotheses
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs) hcomm

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
