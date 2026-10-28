module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Marking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.PointCoreMovement
public import Theory.GroupTheory.PCoreQuotientOrder

/-!
# Point-core movement from an A₇ component of any original local

The component equals O²(I), so its image lies in the component O²(G₁).
The map to the latter's intrinsic two-core quotient has two-group kernel.
Thus the order 2520 divides that quotient order, contradicting the small
component alternatives if O₂(G₁) centralizes the original plane.
This discharges the movement premise for both weight-four source branches.
Source: Aschbacher–Smith 14.7.4(3), 14.7.48 and 14.7.50, pp.1043,1064–1065.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- An actual A₇ component in any original local forces the original point
core to move the plane; the local need not be the full point normalizer. -/
theorem local_alternating_seven_plane_moved_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7)) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨D,hD,_,_⟩ := GuardedSource.local_exists_quasisimple_component
    d h hab structural previous faithful earlier F.H hH
  have hc := (local_component_eq_residual_at d h hab structural previous faithful earlier
    source47 I hI C hC).1
  have hd := (local_component_eq_residual_at d h hab structural previous faithful earlier
    source47 F.H hH D hD).1
  let i : I →* F.H := inclusion hI.2.1
  have hCD : C.map i ≤ D := by
    rw [←hc,←hd]
    exact map_pResidual_le 2 i
  let j : C →* D := (i.comp C.subtype).codRestrict D (fun c =>
    hCD (mem_map_of_mem i c.property))
  have hj : Function.Injective j := by
    intro a b he
    apply Subtype.ext
    apply inclusion_injective hI.2.1
    exact congrArg Subtype.val he
  let f := (QuotientGroup.mk' (pCore 2 D)).comp j
  have hk : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective j hj
  have hdiv := f.pCoreQuotient_card_dvd_of_isPGroup_ker 2 hk
  have hcard : Nat.card (C ⧸ pCore 2 C) = 2520 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  apply plane_moved_of_large_component_at h structural previous faithful D hD
  have hle := Nat.le_of_dvd (Nat.card_pos (α := D ⧸ pCore 2 D)) hdiv
  rw [hcard] at hle
  omega
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
