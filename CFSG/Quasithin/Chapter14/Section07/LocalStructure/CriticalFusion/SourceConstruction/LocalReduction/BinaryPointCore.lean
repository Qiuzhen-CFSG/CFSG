module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinarySeedMarkings
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.MarkedCore
/-!
# The original point core is the inner Sylow in the exchanged branch

The original field-four Borel normalizes L₁, whose nonzero two-perfect
image is invariant under the actual factor exchange. The marked Borel
core theorem identifies its two-core with the full inner Sylow. Core
transport through the same two-group kernel gives the literal image of
O₂(L₁) in H/O₂(H), retaining the actual component orbit.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf. This is the Sylow premise in the non-subnormality
argument on the original reciprocal plane.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original point residual's two-core maps onto the actual inner Sylow. -/
theorem local_nonnormal_component_point_core_sylow
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ S : Sylow 2 (star F (conjugateSpanBy K (T : Subgroup G))),
      (S : Subgroup _).map (star F (conjugateSpanBy K (T : Subgroup G))).subtype =
        star F ((F.Li L 1).pCoreIn 2) := by
  have hEq := (local_nonnormal_component_eq_full_point d h hab structural previous faithful earlier
    I K hI hKI hK hnormal).2.1
  subst I
  have hTI := F.sylow_le_of_mem_Hz hI
  have hm := local_nonnormal_component_field_four d h hab structural previous faithful earlier
    F.H K hI hKI hK hnormal
  have hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K := by
    intro he
    exact hnormal (normal_of_sylow_span_eq F.H K T hKI hTI
      ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
        (local_star_sqtk h F.H hI) hK).imp_right And.left) he)
  obtain ⟨t,ht,htn,hNI,e,S,horbit,he,hres,hS,him,hsol,hLB,hBM,hJB,hBL,hLres,_,_⟩ :=
    local_binary_borel d h hab structural previous faithful earlier F.H K hI hKI hK
      (n := 2) (by decide) hm hmoving
  let N := K ⊔ K.conjBy t
  let B := SourceTorus.chosenLift F.H N hNI S
  let S' := SourceTorus.chosenSylow F.H N e S
  let f := SourceTorus.toBinary F.H N hNI e S
  let D := ((F.Li L 1).subgroupOf B).map f
  let : ((F.Li L 1).subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer hBL
  let : D.Normal := (inferInstance : ((F.Li L 1).subgroupOf B).Normal).map f
    (SourceTorus.toBinary_surjective F.H N hNI e S)
  have hp : IsPPerfect 2 D :=
    ((isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe hLB).symm.toMonoidHom (subgroupOfEquivOfLe hLB).symm.surjective).of_surjective
      (f.subgroupMap _) (f.subgroupMap_surjective _)
  have hk : IsPGroup 2 f.ker := SourceTorus.toBinary_ker_two F.H N hNI e S
  have hne : D ≠ ⊥ := by
    intro hz
    have hle : (F.Li L 1).subgroupOf B ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp hz
    have hpL : IsPGroup 2 (F.Li L 1) :=
      (hk.to_le hle).of_equiv (subgroupOfEquivOfLe hLB)
    obtain ⟨n,hn⟩ := (hpL.to_quotient (pCore 2 (F.Li L 1))).exists_card_eq
    rw [pointResidual_core_quotient_card h structural] at hn
    have hd : 3 ∣ 2^n := hn ▸ dvd_rfl
    have hh := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at hh
  have hi := ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (local_star_sqtk h F.H hI) hK).resolve_left hnormal).1
  have hnN := SourceActions.normalizes_orbit F.H K hKI hi (hTI ht) htn
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) := le_sup_right.trans hJB
  let τ := SourceActions.binaryAction F.H N hNI e S (hTI ht) (hnN (hTI ht)) (hTB ht)
  have hτ := (SourceActions.binary_moving_exchanges F.H K (hTI ht) hNI hi htn e he S
    (hnN (hTI ht)) (hTB ht)).2
  have hD := SourceActions.binary_image_invariant F.H N hNI e S (F.Li L 1)
    (hTI ht) (hnN (hTI ht)) (hTB ht)
    (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural) ht)
  have hc := BorelProjections.normal_swapped_core hm S' τ hτ D hD hne hp
  have hcmap := map_pCoreIn_of_ker_isPGroup f hk ((F.Li L 1).subgroupOf B)
  rw [pCoreIn_subgroupOf 2 _ B hLB] at hcmap
  rw [←hcmap] at hc
  rw [SourceConclusion.binary_image_eq_star_image F.H N hNI e S _
    ((pCoreIn_le 2 _).trans hLB)] at hc
  have hc' : (star F ((F.Li L 1).pCoreIn 2)).subgroupOf (star F N) =
      S.toSubgroup := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact hc
  have hQH : (F.Li L 1).pCoreIn 2 ≤ N :=
    (pCoreIn_le 2 _).trans (hLB.trans (borelLift_le F.H N hNI _))
  have hstar : star F ((F.Li L 1).pCoreIn 2) ≤ star F N :=
    map_mono (subgroupOf_mono F.H hQH)
  have hfinal := congrArg (map (star F N).subtype) hc'
  rw [map_subgroupOf_eq_of_le hstar] at hfinal
  rw [horbit]
  exact ⟨S,hfinal.symm⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
