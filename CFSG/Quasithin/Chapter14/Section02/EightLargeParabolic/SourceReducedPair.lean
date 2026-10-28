module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBorel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairReduced
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The reduced local pair in the normal eight-field branch

The original full Borel normalizes T. Linear Sylow factorization therefore
identifies each DGS reduced local group LᵢT with its starred parabolic.
These starred groups are exactly H and YT, and their Sylows are the original T.
The inclusion of O²(H) gives a quotient equivalence H/O₂(H) ≃ L₂(8)
which agrees with the prescribed eR on every representative. The second
reduced quotient is S₃ and has the same two-core as the full second parabolic.

Applying these equivalences to the literal source pair gives core indices
8 and 2 in T. The reduced second group has index 7 in YT(M ∩ O²(H));
thus its missing odd factor must be restored in the amalgam recognition.
These results supply the reduced local profiles, not the critical-pair,
hexagon, or marked triality recognition theorem.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs, Part II,
(6.0)--(6.1), printed pp.118--119; Aschbacher--Smith F.1.9 and
14.2.14--16, printed pp.261--262 and 984--986. DGS's reduced local groups
are kept distinct from the original F.1.1 factors and the full parabolics.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterF.Source
variable {G : Type*} [Group G] [Finite G]

private theorem linear_localJoin_eq_starred
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (a : (L i ⧸ pCore 2 (L i)) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    L i ⊔ S = starredParabolic L S i := by
  have hs := h.linear_local_sylow_factorization i F a (hn i)
  rw [h.localJoin_twoCore_eq_parabolic hn i] at hs
  change L i ⊔ S = twoCore (parabolic L S i) ⊔ L i
  apply le_antisymm
  · apply sup_le le_sup_right
    exact hs.le.trans (sup_le le_sup_left (inf_le_right.trans le_sup_right))
  · exact sup_le ((h.parabolic_core_le_S i).trans le_sup_right) le_sup_left

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

private theorem local_borel_normalizes (i : Fin 2) :
    borel (locals T M Mc H i) (T : Subgroup G) ≤ normalizer (T : Set G) := by
  have hCB := (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.2.1
  have hB : borel (locals T M Mc H i) (T : Subgroup G) ≤
      commonBorel (locals T M Mc H) (T : Subgroup G) := by
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  exact (hB.trans hCB.le).trans
    (source_borel_normalizes_sylow hG T hempty hM hu hmany hcard e H hH eR)

private theorem local_second_quotient :
    Nonempty ((locals T M Mc H 1 ⧸ pCore 2 (locals T M Mc H 1)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨_, hS, _, _, _⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3, inferInstance, inferInstance,
      GaloisField.card 2 3 (by decide), ⟨eR⟩⟩
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
    (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
  exact (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    (secondSylow T M Mc H) hS le_sup_left hnot).2

/-- The DGS reduced local groups are precisely the original starred parabolics. -/
theorem source_localJoin_eq_starred (i : Fin 2) :
    locals T M Mc H i ⊔ (T : Subgroup G) =
      starredParabolic (locals T M Mc H) (T : Subgroup G) i := by
  have hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  have hn := local_borel_normalizes hG T hempty hM hu hmany hcard e H hH eR
  fin_cases i
  · exact linear_localJoin_eq_starred hF hn 0 (GaloisField 2 3) (residualQuotientEquiv H eR)
  · obtain ⟨a⟩ := local_second_quotient hG T hempty hM hu hmany hcard e H hH eR
    exact linear_localJoin_eq_starred hF hn 1 (ZMod 2)
      ((a.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm).trans
        (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))

/-- Both starred local Sylows are the original T, without assuming T lies in O²(H). -/
theorem source_starredSylow_eq (i : Fin 2) :
    starredSylow (locals T M Mc H) (T : Subgroup G) i = (T : Subgroup G) := by
  have hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  have hS : (T : Subgroup G) ≤ starredParabolic (locals T M Mc H) (T : Subgroup G) i := by
    rw [← source_localJoin_eq_starred hG T hempty hM hu hmany hcard e H hH eR]
    exact le_sup_right
  obtain ⟨U, hU⟩ := hF.starredSylow_isSylow i
  have hle := hF.starredSylow_le_S i
  have hUS : (U : Subgroup (starredParabolic (locals T M Mc H) (T : Subgroup G) i)) ≤
      (T : Subgroup G).subgroupOf (starredParabolic (locals T M Mc H) (T : Subgroup G) i) := by
    apply map_le_iff_le_comap.mp
    exact hU.le.trans hle
  have he := U.is_maximal' T.isPGroup'.comap_subtype hUS
  have hh := congrArg (Subgroup.map
    (starredParabolic (locals T M Mc H) (T : Subgroup G) i).subtype) he
  change ((T : Subgroup G).subgroupOf
    (starredParabolic (locals T M Mc H) (T : Subgroup G) i)).map _ = _ at hh
  rw [map_subgroupOf_eq_of_le hS, hU] at hh
  exact hh.symm

/-- DGS (6.1) gives the exact reduced endpoints H and YT inside the source group. -/
theorem source_starredParabolics :
    starredParabolic (locals T M Mc H) (T : Subgroup G) 0 = H ∧
      starredParabolic (locals T M Mc H) (T : Subgroup G) 1 =
        sourceResidual M Mc ⊔ (T : Subgroup G) := by
  have hS := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).2.1
  constructor
  · rw [← source_localJoin_eq_starred hG T hempty hM hu hmany hcard e H hH eR]
    change residual H ⊔ (T : Subgroup G) = H
    have hh := congrArg (Subgroup.map H.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup] at hh
    change residual H ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype =
      (⊤ : Subgroup H).map H.subtype at hh
    rw [map_subgroupOf_eq_of_le hH.1.1.2, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  · rw [← source_localJoin_eq_starred hG T hempty hM hu hmany hcard e H hH eR]
    change (sourceResidual M Mc ⊔ secondSylow T M Mc H) ⊔ (T : Subgroup G) = _
    rw [sup_assoc, sup_eq_right.mpr hS]

/-- The original first endpoint quotient, extending the specified residual marking. -/
def sourceFirstCoreQuotientEquiv : (H ⧸ pCore 2 H) ≃* Theory.PSL2.BinaryGroup 3 :=
  let hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  let a := (MulEquiv.subgroupCongr
    (source_starredParabolics hG T hempty hM hu hmany hcard e H hH eR).1).symm
  ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (hF.starredQuotientEquiv 0).symm).trans (residualQuotientEquiv H eR)

/-- The first quotient equivalence agrees with the literal eR on every residual element. -/
theorem sourceFirstCoreQuotientEquiv_mk (x : pResidual 2 H) :
    sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR
      (QuotientGroup.mk (x : H)) = eR (QuotientGroup.mk x) := by
  let hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  let xR : residual H := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective x
  change residualQuotientEquiv H eR ((hF.starredQuotientEquiv 0).symm
    (QuotientGroup.mk (inclusion (local_le_starredParabolic 0) xR))) = _
  rw [← hF.starredQuotientEquiv_mk 0 xR, MulEquiv.symm_apply_apply]
  exact residualQuotientEquiv_mk H eR x

/-- The second reduced endpoint has the symmetric-three quotient over its actual core. -/
theorem source_reduced_second_quotient :
    Nonempty (((sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  obtain ⟨a⟩ := local_second_quotient hG T hempty hM hu hmany hcard e H hH eR
  let b := (MulEquiv.subgroupCongr
    (source_starredParabolics hG T hempty hM hu hmany hcard e H hH eR).2).symm
  exact ⟨((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
    (hF.starredQuotientEquiv 1).symm).trans a⟩

/-- The reduced second endpoint has exactly the core of the full second parabolic. -/
theorem source_reduced_second_core :
    (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 =
      (secondParabolic T M Mc H).pCoreIn 2 := by
  have hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  have hh := hF.starredParabolic_same_core 1
  rw [(source_starredParabolics hG T hempty hM hu hmany hcard e H hH eR).2,
    (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.1] at hh
  exact hh

omit [Finite G] hG hempty hM hu hmany hcard e hH eR in
private theorem core_relIndex_self (A : Subgroup G) :
    (A.pCoreIn 2).relIndex A = Nat.card (A ⧸ pCore 2 A) := by
  have hh : (A.pCoreIn 2).subgroupOf A = pCore 2 A :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
  change ((A.pCoreIn 2).subgroupOf A).index = _
  rw [hh, index_eq_card]

private theorem reduced_second_sylow_index :
    (T : Subgroup G).relIndex (sourceResidual M Mc ⊔ (T : Subgroup G)) = 3 := by
  obtain ⟨a⟩ := source_reduced_second_quotient hG T hempty hM hu hmany hcard e H hH eR
  exact SymmetricThreeTwoCore.sylow_index_three a (T.subtype le_sup_right)

/-- The reduced second endpoint has index seven in the full parabolic: its
missing odd factor must be restored by the marked-amalgam argument. -/
theorem source_reduced_second_index :
    (sourceResidual M Mc ⊔ (T : Subgroup G)).relIndex (secondParabolic T M Mc H) = 7 := by
  have hTB : (T : Subgroup G) ≤ H ⊓ M := le_inf hH.1.1.2 hM.1.2
  have hBP : H ⊓ M ≤ secondParabolic T M Mc H := by
    rw [← (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.2.2.1]
    exact inf_le_right
  have hTP : (T : Subgroup G).relIndex (secondParabolic T M Mc H) = 21 := by
    rw [← relIndex_mul_relIndex (T : Subgroup G) (H ⊓ M) _ hTB hBP,
      source_sylow_index_borel hG T hempty hM hu hmany hcard e H hH eR,
      (source_local_degrees hG T hempty hM hu hmany hcard e H hH eR).2]
  have hh := relIndex_mul_relIndex (T : Subgroup G)
    (sourceResidual M Mc ⊔ (T : Subgroup G)) (secondParabolic T M Mc H)
    le_sup_right le_sup_left
  rw [reduced_second_sylow_index hG T hempty hM hu hmany hcard e H hH eR, hTP] at hh
  omega

/-- The source local fields have orders eight and two: these are the exact
indices of the two parabolic cores in the common Sylow. -/
theorem source_core_indices :
    (H.pCoreIn 2).relIndex (T : Subgroup G) = 8 ∧
      ((secondParabolic T M Mc H).pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
  have hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  have hpar := source_parabolics hG T hempty hM hu hmany hcard e H hH eR
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := hF.parabolic_core_le_S 0
    rw [hpar.1] at hh
    exact hh
  constructor
  · have hi : (T : Subgroup G).relIndex H = 63 := by
      rw [← relIndex_mul_relIndex (T : Subgroup G) (H ⊓ M) H
        (le_inf hH.1.1.2 hM.1.2) inf_le_left,
        source_sylow_index_borel hG T hempty hM hu hmany hcard e H hH eR,
        (source_local_degrees hG T hempty hM hu hmany hcard e H hH eR).1]
    have hc : Nat.card (H ⧸ pCore 2 H) = 504 := by
      rw [Nat.card_congr
        (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR).toEquiv,
        ← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).toEquiv,
        GorensteinWalter.sl2_card_formula, GaloisField.card 2 3 (by decide)]
      norm_num
    have hh := relIndex_mul_relIndex (H.pCoreIn 2) (T : Subgroup G) H hQT hH.1.1.2
    rw [hi, core_relIndex_self, hc] at hh
    omega
  · let J := sourceResidual M Mc ⊔ (T : Subgroup G)
    have hJ : J.pCoreIn 2 = (secondParabolic T M Mc H).pCoreIn 2 :=
      source_reduced_second_core hG T hempty hM hu hmany hcard e H hH eR
    have hJT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
      have hh := hF.parabolic_core_le_S 1
      rw [hpar.2.1] at hh
      exact hJ.le.trans hh
    obtain ⟨a⟩ := source_reduced_second_quotient hG T hempty hM hu hmany hcard e H hH eR
    have hc : Nat.card (J ⧸ pCore 2 J) = 6 := by
      rw [Nat.card_congr a.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    have hh := relIndex_mul_relIndex (J.pCoreIn 2) (T : Subgroup G) J hJT le_sup_right
    rw [core_relIndex_self, hc, reduced_second_sylow_index hG T hempty hM hu hmany hcard e H hH eR,
      hJ] at hh
    omega

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
