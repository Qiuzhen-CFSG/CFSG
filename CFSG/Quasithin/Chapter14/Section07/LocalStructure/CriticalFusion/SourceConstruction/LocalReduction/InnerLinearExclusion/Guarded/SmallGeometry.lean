module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.SmallGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.CubicMovingEndgame

/-!
# Original small-quotient exclusion: SmallGeometry

The source proof is specialized to the same G,T structural and escape inputs.
All subgroup restrictions, quotient maps and the actual rank-three system
are retained. The universal public API in the original module is unchanged.
Source: Aschbacher–Smith 14.7.11,49, printed pp.1045–1046,1064,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The residual of the constructed second parabolic escapes the original
normalizer and centralizes the original plane, as required at the start of
14.7.11. No local-containment or plane-centralization premise is supplied. -/
theorem small_local_second_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hm : Nonempty (HStar I ≃* Matrix.PSL3Two.PSL) ∨
      Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (HStar I ≃* Equiv.Perm (Fin 6))) :
    ∃ H₂ Y : Subgroup G, H₂ ≤ I ∧ (T : Subgroup G) ≤ H₂ ∧
      RankTwoParabolics I ((T : Subgroup G).subgroupOf I)
        ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I) (H₂.subgroupOf I) ∧
      Nonempty (HStar H₂ ≃* Equiv.Perm (Fin 3)) ∧
      Y = (pResidual 2 H₂).map H₂.subtype ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧ Y ⊔ (T : Subgroup G) = H₂ ∧
      (F.Li L 1 ⊔ (T : Subgroup G)) ⊔ Y = I ∧
      ¬ Y ≤ normalizer (L : Set G) ∧ ⁅F.Vi 2,Y⁆ = ⊥ := by
  obtain ⟨H₂,h₂I,hT₂,hR,he,hi,hgen⟩ := small_local_second_parabolic_at h structural I hI hm
  let Y := (pResidual 2 H₂).map H₂.subtype
  have hY₂ : Y ≤ H₂ := map_subtype_le _
  have hYn : H₂ ≤ normalizer (Y : Set G) := by
    exact H₂.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H₂ (pResidual 2 H₂))
  have hYp : IsPPerfect 2 Y := isPPerfect_embedded_pResidual 2 H₂
  have hYT : Y ⊔ (T : Subgroup G) = H₂ := by
    have hh := congrArg (map H₂.subtype) (pResidual_sup_sylow_eq_top (T.subtype hT₂))
    simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hT₂,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  have hgenY : (F.Li L 1 ⊔ (T : Subgroup G)) ⊔ Y = I := by
    calc
      (F.Li L 1 ⊔ (T : Subgroup G)) ⊔ Y =
          (F.Li L 1 ⊔ (T : Subgroup G)) ⊔ (Y ⊔ (T : Subgroup G)) := by
        symm
        rw [←sup_assoc]
        exact sup_eq_left.mpr (le_sup_right.trans le_sup_left)
      _ = I := by rw [hYT,hgen]
  have hout : ¬ Y ≤ normalizer (L : Set G) := by
    intro hYM
    apply hI.2.2
    rw [←hgenY]
    exact sup_le (sup_le (((F.Li_le L 1).trans inf_le_left).trans L.le_normalizer)
      (h.sylow_normalizes_at structural)) hYM
  have hc : ⁅F.Vi 2,Y⁆ = ⊥ := by
    have hYH := hY₂.trans (h₂I.trans hI.2.1)
    have heY : Nonempty (HStar (Y ⊔ (T : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := hYT ▸ he
    exact (original_cubic_actor_contained_or_plane_fixed h hab structural previous faithful
      Y hYH hYp (hT₂.trans hYn) heY).resolve_left hout
  exact ⟨H₂,Y,h₂I,hT₂,hR,he,rfl,hYp,hT₂.trans hYn,hYT,hgenY,hout,hc⟩

omit [Finite G] in
private theorem plane_parabolic_eq_intersection :
    F.P L = (L ⊔ (T : Subgroup G)) ⊓ F.Gi 2 := by
  ext x
  simp only [InvariantFlag.P,mem_inf,mem_iInf]
  constructor
  · exact fun hx => ⟨hx.1,hx.2 2 ⟨le_rfl,by decide⟩⟩
  · rintro ⟨hx,h2⟩
    refine ⟨hx,fun i hi => ?_⟩
    have : i = 2 := by omega
    subst i
    exact h2

/-- The constructed second parabolic is precisely the plane stabilizer in I.
Consequently the middle source vertex has the two required literal
intersections; these are conclusions, not supplied amalgam geometry. -/
theorem small_local_middle_intersections
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hm : Nonempty (HStar I ≃* Matrix.PSL3Two.PSL) ∨
      Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (HStar I ≃* Equiv.Perm (Fin 6))) :
    ∃ H₂ Y : Subgroup G, H₂ ≤ I ∧ (T : Subgroup G) ≤ H₂ ∧
      RankTwoParabolics I ((T : Subgroup G).subgroupOf I)
        ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I) (H₂.subgroupOf I) ∧
      Nonempty (HStar H₂ ≃* Equiv.Perm (Fin 3)) ∧
      Y = (pResidual 2 H₂).map H₂.subtype ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧ Y ⊔ (T : Subgroup G) = H₂ ∧
      (F.Li L 1 ⊔ (T : Subgroup G)) ⊔ Y = I ∧
      ¬ Y ≤ normalizer (L : Set G) ∧ ⁅F.Vi 2,Y⁆ = ⊥ ∧
      H₂ = I ⊓ F.Gi 2 ∧
      (H₂ ⊔ F.P L) ⊓ I = H₂ ∧
      (H₂ ⊔ F.P L) ⊓ (L ⊔ (T : Subgroup G)) = F.P L ∧
      (H₂ ⊔ F.P L) ⊓ I ⊓ (L ⊔ (T : Subgroup G)) = (T : Subgroup G) := by
  obtain ⟨H₂,Y,h₂I,hT₂,hR,he,hY,hYp,hYn,hYT,hgen,hout,hc⟩ :=
    small_local_second_residual h hab structural previous faithful I hI hm
  have hYplane : Y ≤ F.Gi 2 :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (Subgroup.centralizer_le_normalizer _)
  have h₂plane : H₂ ≤ F.Gi 2 := by
    rw [←hYT]
    exact sup_le hYplane (F.invariant 2)
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  have hBI : B ≤ I := sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)
  have hBLT : B ≤ L ⊔ (T : Subgroup G) :=
    sup_le ((F.Li_le L 1).trans (inf_le_left.trans le_sup_left)) le_sup_right
  have hnot : ¬ I ≤ F.Gi 2 := by
    intro hIG
    have hBP : B ≤ F.P L := by
      rw [plane_parabolic_eq_intersection]
      exact le_inf hBLT (hBI.trans hIG)
    have hBT : B ≤ (T : Subgroup G) :=
      (le_inf hBP (hBI.trans hI.2.1)).trans_eq (plane_parabolic_inf_point h structural)
    have hbe : B = (T : Subgroup G) := le_antisymm hBT le_sup_right
    have hi := SymmetricThreeTwoCore.sylow_index_three
      (pointQuotientEquiv_at h structural) (T.subtype (show (T : Subgroup G) ≤ B from le_sup_right))
    change (T : Subgroup G).relIndex B = 3 at hi
    rw [hbe,relIndex_self] at hi
    omega
  have hDtop : (F.Gi 2).subgroupOf I ≠ ⊤ := by
    intro htop
    apply hnot
    intro x hx
    have hh : (⟨x,hx⟩ : I) ∈ (F.Gi 2).subgroupOf I := htop ▸ mem_top _
    exact hh
  have hEq : H₂.subgroupOf I = (F.Gi 2).subgroupOf I := by
    by_contra hne
    exact hDtop (hR.right_maximal.2 _ (lt_of_le_of_ne (subgroupOf_mono I h₂plane) hne))
  have h₂eq : H₂ = I ⊓ F.Gi 2 := by
    have hh := congrArg (map I.subtype) hEq
    rw [map_subgroupOf_eq_of_le h₂I,subgroupOf_map_subtype,inf_comm] at hh
    exact hh
  have hJplane : H₂ ⊔ F.P L ≤ F.Gi 2 :=
    sup_le h₂plane (F.P_le_G₂ (by decide) L h.chosen.normalizes)
  have hJI : (H₂ ⊔ F.P L) ⊓ I = H₂ := by
    apply le_antisymm
    · exact (le_inf inf_le_right (inf_le_left.trans hJplane)).trans h₂eq.ge
    · exact le_inf le_sup_left h₂I
  have hJLT : (H₂ ⊔ F.P L) ⊓ (L ⊔ (T : Subgroup G)) = F.P L := by
    apply le_antisymm
    · exact (le_inf inf_le_right (inf_le_left.trans hJplane)).trans_eq
        plane_parabolic_eq_intersection.symm
    · exact le_inf le_sup_right inf_le_left
  have hchamber : (H₂ ⊔ F.P L) ⊓ I ⊓ (L ⊔ (T : Subgroup G)) = (T : Subgroup G) := by
    apply le_antisymm
    · have hle : (H₂ ⊔ F.P L) ⊓ I ⊓ (L ⊔ (T : Subgroup G)) ≤ F.P L ⊓ F.H :=
        le_inf ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans_eq hJLT)
          (inf_le_left.trans (inf_le_right.trans hI.2.1))
      exact hle.trans_eq (plane_parabolic_inf_point h structural)
    · exact le_inf (le_inf (hT₂.trans le_sup_left) (F.sylow_le_of_mem_Hz hI)) le_sup_right
  exact ⟨H₂,Y,h₂I,hT₂,hR,he,hY,hYp,hYn,hYT,hgen,hout,hc,h₂eq,hJI,hJLT,hchamber⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
