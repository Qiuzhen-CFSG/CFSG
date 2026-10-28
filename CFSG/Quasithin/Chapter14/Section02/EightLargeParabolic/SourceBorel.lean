module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Setup
public import Theory.GroupTheory.PCoreQuotientBorelNormalizer
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.SpecificGroups.PSL2.OrdinaryBorelGeometry
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The full Borel and local degrees of the normal eight-field source pair

Before recognizing the amalgam, the literal quotient of O²(H) identifies
its Sylow normalizer indices as 9 and 7. The symmetric-three quotient of
YS₂ gives the opposite local degree 3. Normalized product formulas carry
these indices to H, YT(M ∩ O²(H)), and their full overlap H ∩ M.
The odd outer automorphism order of L₂(8) makes that overlap normalize the
original T; its embedded two-core is therefore T. In particular the whole
odd factor of order seven survives in the overlap.

These calculations supply the local degrees and the 2-closed Borel for the
DGS recognition argument. They do not assert the marked triality isomorphism.
Source: Aschbacher--Smith 14.2.14--16, pp.984--986; Delgado--Goldschmidt--
Stellmacher, Groups and Graphs, Part II, Hypothesis A and B, pp.94--96,
and the 2-closed case of (15.2), pp.226--227.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source
variable {G : Type*} [Group G] [Finite G]

/-- The prescribed intrinsic residual quotient, transported to its ambient copy. -/
def residualQuotientEquiv (H : Subgroup G)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3) :
    (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.BinaryGroup 3 :=
  let a := ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eR

omit [Finite G] in
/-- The transport uses exactly the given residual quotient marking on representatives. -/
@[simp] theorem residualQuotientEquiv_mk (H : Subgroup G)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
    (x : pResidual 2 H) :
    residualQuotientEquiv H eR
      (QuotientGroup.mk ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective x)) =
      eR (QuotientGroup.mk x) := by
  change eR (QuotientGroup.mk
    (((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
      ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective x))) = _
  rw [MulEquiv.symm_apply_apply]

private theorem eight_sylow_indices {D : Type*} [Group D] [Finite D]
    (eD : (D ⧸ pCore 2 D) ≃* Theory.PSL2.BinaryGroup 3) (P : Sylow 2 D) :
    (normalizer (P : Set D)).index = 9 ∧
      (P : Subgroup D).relIndex (normalizer (P : Set D)) = 7 := by
  let q := eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := eD.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 D := by
    ext d
    change eD (QuotientGroup.mk d) = 1 ↔ d ∈ pCore 2 D
    rw [eD.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hkP : q.ker ≤ (P : Subgroup D) := hk ▸ pCore_isPGroup.le_sylow_of_normal P
  let U := P.mapSurjective hq
  have hU : Nat.card U = 8 := by
    rw [Theory.PSL2.OrdinaryBorel.sylow_card]
    exact GaloisField.card 2 3 (by decide)
  have hNU : Nat.card (normalizer (U : Set (Theory.PSL2.BinaryGroup 3))) = 56 := by
    rw [Nat.card_congr
      (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv
        (GaloisField 2 3) U).toEquiv,
      Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.card_borel,
      GaloisField.card 2 3 (by decide)]
    norm_num
  have hD : Nat.card (Theory.PSL2.BinaryGroup 3) = 504 := by
    rw [← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).toEquiv,
      GorensteinWalter.sl2_card_formula, GaloisField.card 2 3 (by decide)]
    norm_num
  have hiU : U.index = 63 := by
    have hh := (U : Subgroup (Theory.PSL2.BinaryGroup 3)).index_mul_card
    rw [hU, hD] at hh
    omega
  have hiN : (normalizer (U : Set (Theory.PSL2.BinaryGroup 3))).index = 9 := by
    have hh := (normalizer (U : Set (Theory.PSL2.BinaryGroup 3))).index_mul_card
    rw [hNU, hD] at hh
    omega
  have hiP : P.index = 63 :=
    ((P : Subgroup D).index_map_eq hq hkP).symm.trans hiU
  have hi : (normalizer (P : Set D)).index = 9 := by
    rw [← (normalizer (P : Set D)).index_map_eq hq (hkP.trans P.le_normalizer),
      P.normalizer_map_surjective q hq]
    exact hiN
  refine ⟨hi, ?_⟩
  have hh := relIndex_mul_index (P : Subgroup D).le_normalizer
  change (P : Subgroup D).relIndex (normalizer (P : Set D)) *
    (normalizer (P : Set D)).index = P.index at hh
  rw [hi, hiP] at hh
  omega

private theorem parabolic_borel_index {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (i : Fin 2) :
    (commonBorel L S).relIndex (parabolic L S i) = (borel (L i) S).relIndex (L i) := by
  rw [parabolic_eq_sup_commonBorel,
    relIndex_sup_of_normalizes _ _ (h.commonBorel_normalizes_local i),
    ← inf_relIndex_right, inf_comm (commonBorel L S), h.local_inf_commonBorel]

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

private theorem local_borel_indices :
    (borel (residual H) (T : Subgroup G)).relIndex (residual H) = 9 ∧
      (T : Subgroup G).relIndex (borel (residual H) (T : Subgroup G)) = 7 := by
  have hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  obtain ⟨P, hP⟩ := (show ∃ P : Sylow 2 (residual H),
    (P : Subgroup (residual H)).map (residual H).subtype = (T : Subgroup G) ⊓ residual H
      from hF.sylow 0)
  change (P : Subgroup (residual H)).map (residual H).subtype =
    (T : Subgroup G) ⊓ residual H at hP
  have hB := borel_subgroupOf_eq_sylowNormalizer (residual H) (T : Subgroup G) P hP
  have hPN := eight_sylow_indices (residualQuotientEquiv H eR) P
  constructor
  · change ((borel (residual H) (T : Subgroup G)).subgroupOf (residual H)).index = 9
    rw [hB]
    exact hPN.1
  · have hPS : (T : Subgroup G).subgroupOf (residual H) = (P : Subgroup (residual H)) := by
      apply map_injective (residual H).subtype_injective
      rw [subgroupOf_map_subtype, hP]
    rw [← relIndex_subgroupOf (borel_le (residual H) (T : Subgroup G)), hPS, hB]
    exact hPN.2

/-- The two original endpoints have local degrees nine and three over the entire
intersection. No marked realization is used. -/
theorem source_local_degrees :
    (H ⊓ M).relIndex H = 9 ∧
      (H ⊓ M).relIndex (secondParabolic T M Mc H) = 3 := by
  obtain ⟨hF, hS, _, _, hB₂⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  obtain ⟨hzero, hone, hCB, _, _⟩ := source_parabolics hG T hempty hM hu hmany hcard e H hH eR
  constructor
  · have hi := parabolic_borel_index hF 0
    rw [hCB, hzero] at hi
    exact hi.trans (local_borel_indices hG T hempty hM hu hmany hcard e H hH eR).1
  · have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
      .linear 3 (by decide) ⟨GaloisField 2 3, inferInstance, inferInstance,
        GaloisField.card 2 3 (by decide), ⟨eR⟩⟩
    have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
      (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
    obtain ⟨_, ⟨eJ⟩⟩ := source_residual_actor_movement hG T hempty hM hu hmany hcard e
      (secondSylow T M Mc H) hS le_sup_left hnot
    obtain ⟨hinter, P, hP⟩ := source_residual_actor_sylow hG T hempty hM hu hmany hcard e
      (secondSylow T M Mc H) hS le_sup_left
    have hPS : (secondSylow T M Mc H).subgroupOf
        (sourceResidual M Mc ⊔ secondSylow T M Mc H) = (P : Subgroup _) := by
      apply map_injective (sourceResidual M Mc ⊔ secondSylow T M Mc H).subtype_injective
      rw [map_subgroupOf_eq_of_le le_sup_right, hP]
    rw [← hone, ← hCB, parabolic_borel_index hF]
    change (borel (sourceResidual M Mc ⊔ secondSylow T M Mc H) (T : Subgroup G)).relIndex
      (sourceResidual M Mc ⊔ secondSylow T M Mc H) = 3
    rw [hB₂, relIndex, hPS]
    exact SymmetricThreeTwoCore.sylow_index_three eJ P

/-- The full odd Borel factor has order seven, measured above the original T. -/
theorem source_sylow_index_borel : (T : Subgroup G).relIndex (H ⊓ M) = 7 := by
  obtain ⟨hF, hS, _, hB, hB₂⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hCB := (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.2.1
  rw [← hCB]
  change (T : Subgroup G).relIndex
    (borel (residual H) (T : Subgroup G) ⊔
      borel (sourceResidual M Mc ⊔ secondSylow T M Mc H) (T : Subgroup G) ⊔
        (T : Subgroup G)) = 7
  have hn : (T : Subgroup G) ≤ normalizer (borel (residual H) (T : Subgroup G) : Set G) :=
    hF.S_normalizes_borel 0
  rw [hB₂, sup_assoc, sup_eq_right.mpr hS, relIndex_sup_of_normalizes _ _ hn]
  exact (local_borel_indices hG T hempty hM hu hmany hcard e H hH eR).2

/-- The full source Borel normalizes T, including its part outside O²(H). -/
theorem source_borel_normalizes_sylow : H ⊓ M ≤ normalizer (T : Set G) := by
  obtain ⟨hF, hS, _, hB, hB₂⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  let a := residualQuotientEquiv H eR
  have hz : center (residual H ⧸ pCore 2 (residual H)) = ⊥ := by
    let f := a.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
    apply eq_bot_iff.mpr
    intro d hd
    have hf : f d ∈ center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
      (centerCongr f ⟨d, hd⟩).property
    rw [Theory.PSL2.sl2_center_eq_bot, mem_bot] at hf
    exact f.injective (hf.trans f.map_one.symm)
  have ho : Nat.Coprime 2 (Nat.card (MulAut.Outer (residual H ⧸ pCore 2 (residual H)))) := by
    rw [Nat.card_congr (MulAut.outerCongr a).toEquiv, Theory.PSL2.psl_eight_outer_card]
    decide
  obtain ⟨P, hP⟩ := (show ∃ P : Sylow 2 (residual H),
    (P : Subgroup (residual H)).map (residual H).subtype = (T : Subgroup G) ⊓ residual H
      from hF.sylow 0)
  have hPS : (P : Subgroup (residual H)) = (T : Subgroup G).subgroupOf (residual H) := by
    apply map_injective (residual H).subtype_injective
    rw [subgroupOf_map_subtype]
    exact hP
  have hn := sylow_normalizer_le_of_coprime_outer T (residual H) (hF.S_normalizes 0) hz ho P hPS
  have hb := borel_subgroupOf_eq_sylowNormalizer (residual H) (T : Subgroup G) P hP
  change (borel (residual H) (T : Subgroup G)).subgroupOf (residual H) =
    normalizer (P : Set (residual H)) at hb
  have hbN : borel (residual H) (T : Subgroup G) ≤ normalizer (T : Set G) := by
    rw [← hb, map_subgroupOf_eq_of_le (borel_le _ _)] at hn
    exact hn
  have hCB := (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.2.1
  rw [← hCB]
  exact sup_le (sup_le hbN (hB₂.le.trans (hS.trans T.le_normalizer))) T.le_normalizer

/-- The 2-closed source Borel has precisely the original Sylow as its embedded core. -/
theorem source_borel_twoCore : (H ⊓ M).pCoreIn 2 = (T : Subgroup G) := by
  have hTB : (T : Subgroup G) ≤ H ⊓ M := le_inf hH.1.1.2 hM.1.2
  have hn := source_borel_normalizes_sylow hG T hempty hM hu hmany hcard e H hH eR
  have ht : (T : Subgroup G) ≤ (H ⊓ M).pCoreIn 2 :=
    le_pCoreIn_of_normalizes T.isPGroup' hTB hn
  exact T.is_maximal' (isPGroup_pCoreIn 2 (H ⊓ M)) ht

/-- The odd Cartan factor is an actual subgroup of M ∩ O²(H), disjoint from
T and supplementing T to the whole overlap. -/
theorem source_borel_seven_complement :
    ∃ D : Subgroup G, D ≤ M ⊓ residual H ∧ Nat.card D = 7 ∧
      Disjoint (T : Subgroup G) D ∧ (T : Subgroup G) ⊔ D = H ⊓ M := by
  obtain ⟨hF, hS, _, hB, hB₂⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  obtain ⟨D, hDB, _, _, hd, hsup⟩ := (hF.rankOneBorelFacts 0).abelian_odd_complement
  change D ≤ borel (residual H) (T : Subgroup G) at hDB
  change ((T : Subgroup G) ⊓ residual H) ⊔ D =
    borel (residual H) (T : Subgroup G) at hsup
  have hDR : D ≤ residual H := hDB.trans (borel_le _ _)
  have hdT : Disjoint (T : Subgroup G) D := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    exact hd.le_bot ⟨⟨hx.1, hDR hx.2⟩, hx.2⟩
  have hCB := (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.2.1
  have hs : (T : Subgroup G) ⊔ D = H ⊓ M := by
    rw [← hCB]
    change _ = borel (residual H) (T : Subgroup G) ⊔
      borel (sourceResidual M Mc ⊔ secondSylow T M Mc H) (T : Subgroup G) ⊔
        (T : Subgroup G)
    rw [hB₂, sup_assoc, sup_eq_right.mpr hS, ← hsup]
    exact le_antisymm (sup_le le_sup_right (le_sup_right.trans le_sup_left))
      (sup_le (sup_le (inf_le_left.trans le_sup_left) le_sup_right) le_sup_left)
  have hn : D ≤ normalizer (T : Set G) :=
    (le_sup_right.trans hs.le).trans
      (source_borel_normalizes_sylow hG T hempty hM hu hmany hcard e H hH eR)
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint (T : Subgroup G) D hn hdT
  rw [hs] at hc
  have hi := relIndex_mul_card_of_le (le_inf hH.1.1.2 hM.1.2)
  rw [source_sylow_index_borel hG T hempty hM hu hmany hcard e H hH eR] at hi
  have hD : Nat.card D = 7 := by
    have hp := Nat.card_pos (α := T)
    nlinarith
  exact ⟨D, hB ▸ hDB, hD, hdT, hs⟩

/-- DGS (15.1) makes no reduction of the Borel in this branch: the two starred
intersections and the Borel two-core generate the whole original overlap. -/
theorem source_reduced_borel_eq :
    ((H ⊓ M) ⊓ starredParabolic (locals T M Mc H) (T : Subgroup G) 0) ⊔
      ((H ⊓ M) ⊓ starredParabolic (locals T M Mc H) (T : Subgroup G) 1) ⊔
      (H ⊓ M).pCoreIn 2 = H ⊓ M := by
  obtain ⟨D, hD, _, _, hs⟩ := source_borel_seven_complement
    hG T hempty hM hu hmany hcard e H hH eR
  rw [source_borel_twoCore hG T hempty hM hu hmany hcard e H hH eR]
  apply le_antisymm
  · exact sup_le (sup_le inf_le_left inf_le_left) (le_inf hH.1.1.2 hM.1.2)
  · apply hs.ge.trans
    apply sup_le le_sup_right
    apply le_trans _ (le_sup_left.trans le_sup_left)
    exact le_inf (le_sup_right.trans hs.le)
      (hD.trans (inf_le_right.trans (show residual H ≤ starredParabolic (locals T M Mc H) (T : Subgroup G) 0 from
        local_le_starredParabolic (L := locals T M Mc H) (S := (T : Subgroup G)) 0)))

/-- The literal product in DGS Hypothesis B, with the whole odd Borel retained.
Relative normality of both starred factors justifies the product notation. -/
theorem source_reduced_borel_product :
    (((H ⊓ M) ⊓ starredParabolic (locals T M Mc H) (T : Subgroup G) 0 : Subgroup G) : Set G) *
      (((H ⊓ M) ⊓ starredParabolic (locals T M Mc H) (T : Subgroup G) 1 : Subgroup G) : Set G) *
      ((T : Subgroup G) : Set G) = (H ⊓ M : Subgroup G) := by
  have hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  have hCB := (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.2.1
  have hn (i : Fin 2) : H ⊓ M ≤ normalizer
      (((H ⊓ M) ⊓ starredParabolic (locals T M Mc H) (T : Subgroup G) i : Subgroup G) : Set G) := by
    apply (le_inf (H ⊓ M).le_normalizer ?_).trans inf_normalizer_le_normalizer_inf
    have hp : H ⊓ M ≤ parabolic (locals T M Mc H) (T : Subgroup G) i :=
      hCB.symm.le.trans (commonBorel_le_parabolic i)
    exact hp.trans ((normal_subgroupOf_iff_le_normalizer (starredParabolic_le i)).mp
      (hF.starredParabolic_normal i))
  have hTB : (T : Subgroup G) ≤ H ⊓ M := le_inf hH.1.1.2 hM.1.2
  rw [← coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans (hn 0)),
    ← coe_mul_of_right_le_normalizer_left _ _
      ((le_inf (hTB.trans (hn 0)) (hTB.trans (hn 1))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _))]
  have he := source_reduced_borel_eq hG T hempty hM hu hmany hcard e H hH eR
  rw [source_borel_twoCore hG T hempty hM hu hmany hcard e H hH eR] at he
  exact congrArg (fun A : Subgroup G => (A : Set G)) he

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
