module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NaturalRecognition
public import Theory.GroupTheory.PResidual.CyclicThree
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Excluding cyclic three-group residuals at the original point normalizer

A critical path gives a reciprocal conjugate of U in R₁. If R₁ were
contained in O₂(H), transporting back would put U inside the reciprocal
core, contrary to criticality. Thus R₁ has nontrivial image under the
literal star map. The point-parabolic image has order six times its
two-core order, so every Sylow two-subgroup of H/O₂(H) has order divisible
by four. A cyclic three-group two-residual would instead give Sylow
order at most two.

The canonical equivalence K/O₂(K) ≃ O²(H/O₂(H)) retains the original
quotient map on representatives. It transfers the exclusion to the exact
residual used by the source construction. The final conditional application
removes this cyclic alternative from a prospective residual classification.
It does not prove the remaining residual alternatives.

Here H is the original point normalizer F.H. The full source 14.7.8 also
quantifies over smaller members of H_z. The only explicit earlier source
inputs in the original-group application are Structural1222 and the full
12.2.13 escape theorem; neither a critical path nor a recognized model is
assumed there.

Source: Aschbacher–Smith, 14.7.8, printed p.1045; the critical geometry
of F.8.7 and the residual alternatives of 14.7.52, printed p.1065.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

/-- Reciprocal criticality prevents the original point core from lying in O₂(H). -/
theorem point_core_not_le_H_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) : ¬ F.Ri L 1 ≤ F.H.pCoreIn 2 := by
  intro hle
  obtain ⟨g, _, hHg, hAR⟩ := exists_terminal_edge_transport h structural c
  let f := (MulAut.conj g).toMonoidHom
  have hQmap : c.Qα.map f = F.H.pCoreIn 2 := by
    change ((conjugate F.H c.conjugator).pCoreIn 2).map f = _
    rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective, hHg]
  exact critical_span_not_le_reciprocal_core c
    ((map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
      ((hAR.trans hle).trans_eq hQmap.symm))

/-- The original R₁ has nontrivial image in the literal star quotient. -/
theorem point_core_star_nontrivial
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) : star F (F.Ri L 1) ≠ ⊥ := by
  intro hz
  have hRH : F.Ri L 1 ≤ F.H := (pCoreIn_le 2 B).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
  have hk : (F.Ri L 1).subgroupOf F.H ≤ pCore 2 F.H := by
    simpa only [CriticalFusion.Source.star, Subgroup.map_eq_bot_iff, starMap, QuotientGroup.ker_mk'] using hz
  apply point_core_not_le_H_core h structural c
  intro x hx
  exact mem_map_of_mem F.H.subtype (hk (show (⟨x,hRH hx⟩ : F.H) ∈
    (F.Ri L 1).subgroupOf F.H from hx))

/-- The point-parabolic image forces four to divide every star Sylow order. -/
theorem four_dvd_star_sylow_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (S : Sylow 2 (HStar F.H)) :
    4 ∣ Nat.card S := by
  have hBH : B ≤ F.H :=
    sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  let f : B →* HStar F.H := (starMap F).comp (inclusion hBH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((starMap F).ker.comap (inclusion hBH))
    rw [show (starMap F).ker = pCore 2 F.H from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hBH)
  have hr := point_image_ratio h structural f hk
  have him : (pCore 2 B).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 B).Normal).map _ f.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  have hne : pCore 2 f.range ≠ ⊥ := by
    intro he
    apply point_core_not_le_H_core h structural c
    rintro x ⟨x,hx,rfl⟩
    have hzero : f.rangeRestrict x = 1 :=
      mem_bot.mp (he ▸ him (mem_map_of_mem _ hx))
    have hxcore : inclusion hBH x ∈ pCore 2 F.H :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hzero)
    exact mem_map_of_mem F.H.subtype hxcore
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := f.range)).exists_card_eq
  have hn0 : n ≠ 0 := by
    intro hz
    exact hne (eq_bot_of_card_eq _ (by simpa only [hz, pow_zero] using hn))
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hd : 4 ∣ Nat.card f.range := by
    rw [hr, hn, pow_succ]
    exact ⟨3 * 2 ^ k, by ring⟩
  exact S.pow_dvd_card_of_pow_dvd_card (n := 2)
    (hd.trans f.range.card_subgroup_dvd_card)

/-- The original star quotient cannot have cyclic three-group two-residual. -/
theorem no_cyclic_three_star_residual_of_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G)) :
    ¬ (IsCyclic (pResidual 2 (HStar F.H)) ∧ IsPGroup 3 (pResidual 2 (HStar F.H))) := by
  rintro ⟨hcyc,hthree⟩
  let := hcyc
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  obtain ⟨c⟩ := exists_criticalPath h hab hescape structural uniqueness
  let S : Sylow 2 (HStar F.H) := Classical.choice inferInstance
  have hb := Sylow.card_le_two_of_cyclic_three_residual S (pCore_quotient_pCore_eq_bot 2) hthree
  have hd := four_dvd_star_sylow_card h structural c S
  have hp := Nat.card_pos (α := S)
  have := Nat.le_of_dvd hp hd
  omega

/-- The canonical residual comparison through the original map H → H/O₂(H). -/
noncomputable def residualStarEquiv (F : InvariantFlag T V 3) :
    ((K F) ⧸ pCore 2 (K F)) ≃* pResidual 2 (HStar F.H) := by
  let E : K F ≃* pResidual 2 F.H :=
    (subgroupOfEquivOfLe (show K F ≤ F.H from map_subtype_le _)).symm.trans
      (MulEquiv.subgroupCongr (residual_subgroupOf F))
  let Q := QuotientGroup.congr (pCore 2 (K F)) (pCore 2 (pResidual 2 F.H))
    E (pCore_map_iso 2 E)
  have hc : pCore 2 (pResidual 2 F.H) =
      (pCore 2 F.H).subgroupOf (pResidual 2 F.H) :=
    pCore_subnormal_eq_comap 2 (inferInstance : (pResidual 2 F.H).Normal).isSubnormal
  exact Q.trans ((QuotientGroup.quotientMulEquivOfEq hc).trans
    (pResidualQuotientEquiv 2 (pCore 2 F.H)))

set_option backward.isDefEq.respectTransparency false in
/-- The residual comparison sends an original representative to its star image. -/
theorem residualStarEquiv_mk (F : InvariantFlag T V 3) (k : K F) :
    (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) =
      starMap F ⟨k, (map_subtype_le _ : K F ≤ F.H) k.property⟩ := by
  dsimp only [residualStarEquiv, MulEquiv.trans_apply]
  rw [QuotientGroup.congr_mk']
  change (pResidualQuotientEquiv 2 (pCore 2 F.H)
    (QuotientGroup.mk' ((pCore 2 F.H).subgroupOf (pResidual 2 F.H))
      (((subgroupOfEquivOfLe (show K F ≤ F.H from map_subtype_le _)).symm.trans
        (MulEquiv.subgroupCongr (residual_subgroupOf F))) k)) : HStar F.H) = _
  rw [pResidualQuotientEquiv_mk]
  rfl

/-- The cyclic three-group exclusion on the literal K/O₂(K). -/
theorem no_cyclic_three_residual_of_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G)) :
    ¬ (IsCyclic ((K F) ⧸ pCore 2 (K F)) ∧ IsPGroup 3 ((K F) ⧸ pCore 2 (K F))) := by
  rintro ⟨hcyc,hthree⟩
  let := hcyc
  let e := residualStarEquiv F
  exact no_cyclic_three_star_residual_of_escape h hab structural hescape
    ⟨isCyclic_of_surjective e e.surjective, hthree.of_equiv e⟩

/-- Apply the cyclic exclusion with escape supplied by the full earlier 12.2.13 theorem. -/
theorem no_cyclic_three_residual_of_earlier_source
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ¬ (IsCyclic ((K F) ⧸ pCore 2 (K F)) ∧ IsPGroup 3 ((K F) ⧸ pCore 2 (K F))) :=
  no_cyclic_three_residual_of_escape h hab structural (h.flag_escape F previous)

/-- The original source-data consumer discharges the cyclic three-group branch.
The other residual alternatives and the independent G₂ exclusion remain explicit. -/
theorem exists_data_of_cyclic_or_residual_alternatives
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hcandidates :
      (IsCyclic ((K F) ⧸ pCore 2 (K F)) ∧ IsPGroup 3 ((K F) ⧸ pCore 2 (K F))) ∨
      AlternatingResidual F ∨ G2Residual F)
    (h53 : ¬ G2Residual F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  have h52 : AlternatingResidual F ∨ G2Residual F := hcandidates.resolve_left
    (no_cyclic_three_residual_of_earlier_source h hab structural previous)
  exact exists_data_of_residual_alternatives d h hab structural h52 h53

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
