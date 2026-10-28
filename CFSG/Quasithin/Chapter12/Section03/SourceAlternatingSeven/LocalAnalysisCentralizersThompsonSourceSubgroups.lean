module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceSplitting
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsTransport

/-!
# Restricting the A₇ omega-center splitting to the point residual

For B ≤ L the original two-core O₂(LT) lies in O₂(BT), since it lies in T
and is normalized by BT. Conversely, the center of O₂(BT) centralizes V
and lies in T, hence lies in C_T(V)=O₂(LT). Thus the smaller local group's
omega center is obtained by taking fixed points in the already split
omega center of O₂(LT).

The original L-fixed factor centralizes T and survives this restriction.
This reduces the second omega-center assertion of 12.3.7 to a calculation
inside the actual chosen module V. The last theorem applies the reduction
to the literal perfect residual C_L(e(2))∞, retaining both embedded cores.

Source: Aschbacher--Smith, Lemma 12.3.7(2), printed p.809. The full Thompson
and fixed-space calculation remain with qt-d-1237-thompson-omega; the
weight-six premise is discharged by qt-d-1236-six-component-rigidity and
qt-d-1236-1238-point-centralizers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace Setup.NaturalCoordinates
variable (E : S.NaturalCoordinates)

omit [Finite G] in
theorem subjoin_core_le_sylow (B : Subgroup G) :
    (B ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (B ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

omit [Finite G] in
theorem core_le_subjoin_core (B : Subgroup G) (hBL : B ≤ L) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (B ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
    ((subjoin_core_le_sylow (T := T) L).trans le_sup_right)
  exact (sup_le_sup_right hBL _).trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

include S in
theorem subjoin_core_center_le_core
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (B : Subgroup G) (hBL : B ≤ L) :
    centerIn ((B ⊔ (T : Subgroup G)).pCoreIn 2) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hVQ : V ≤ (B ⊔ (T : Subgroup G)).pCoreIn 2 :=
    S.chosen.le_core.trans (core_le_subjoin_core B hBL)
  rw [← RecognitionSource.chosen_sylow_centralizer_eq_core S.hypothesis S.chosen structural]
  exact le_inf (inf_le_left.trans (subjoin_core_le_sylow B))
    (inf_le_right.trans (centralizer_le hVQ))

include S in
theorem subjoin_core_omega_eq_inf
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (B : Subgroup G) (hBL : B ≤ L) :
    omegaCenterIn ((B ⊔ (T : Subgroup G)).pCoreIn 2) =
      omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓
        centralizer ((B ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
  omegaCenterIn_eq_inf_of_center_le _ _ (core_le_subjoin_core B hBL)
    (subjoin_core_center_le_core (S := S) structural B hBL)

include S in
theorem sylow_component_fixed_le_subjoin_omega
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (B : Subgroup G) (hBL : B ≤ L) :
    omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      omegaCenterIn ((B ⊔ (T : Subgroup G)).pCoreIn 2) := by
  intro c hc
  have hcz := (mem_omegaCenterIn_iff _ _).mp hc.1
  have hcQ : c ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← RecognitionSource.chosen_sylow_centralizer_eq_core S.hypothesis S.chosen structural]
    exact ⟨hcz.1,centralizer_le S.chosen.le_component hc.2⟩
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨core_le_subjoin_core B hBL hcQ,
      centralizer_le (subjoin_core_le_sylow B) hcz.2.1,hcz.2.2⟩

theorem subjoin_core_omega_decomposition_of_weight_six
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBL : B ≤ L) :
    omegaCenterIn ((B ⊔ (T : Subgroup G)).pCoreIn 2) =
      (V ⊓ centralizer ((B ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) ⊔
        (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    Disjoint (V ⊓ centralizer ((B ⊔ (T : Subgroup G)).pCoreIn 2 : Set G))
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let U := omegaCenterIn ((B ⊔ (T : Subgroup G)).pCoreIn 2)
  let C := omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hCU : C ≤ U := sylow_component_fixed_le_subjoin_omega (S := S) structural B hBL
  have hVU : V ⊓ centralizer ((B ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ U := by
    intro v hv
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨core_le_subjoin_core B hBL (S.chosen.le_core hv.1),hv.2,
        ((mem_omegaCenterIn_iff _ _).mp (chosen_le_core_omega (S := S) hv.1)).2.2⟩
  refine ⟨le_antisymm ?_ (sup_le hVU hCU),E.core_omega_factors_disjoint.mono_left inf_le_left⟩
  intro x hx
  have hx' : x ∈ V ⊔ C := by
    rw [← (E.core_omega_decomposition_of_weight_six structural escape hsix).1]
    exact (subjoin_core_omega_eq_inf (S := S) structural B hBL ▸ hx).1
  have hCV : C ≤ normalizer (V : Set G) :=
    (inf_le_right.trans (centralizer_le S.chosen.le_component)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hmul : x ∈ (V : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left V C hCV]
    exact hx'
  obtain ⟨v,hv,c,hc,rfl⟩ := Set.mem_mul.mp hmul
  have hvU : v ∈ U := by
    have hm := U.mul_mem hx (U.inv_mem (hCU hc))
    simpa only [mul_inv_cancel_right] using hm
  exact mul_mem_sup ⟨hv,((mem_omegaCenterIn_iff _ _).mp hvU).2.1⟩ hc
omit [Finite G] in
/-- The literal Sylow-central fixed factor is in the core omega center. -/
theorem sylow_fixed_le_subjoin_omega (B : Subgroup G) :
    omegaCenterIn (T : Subgroup G) ⊓ centralizer (B : Set G) ≤
      omegaCenterIn ((B ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let F := omegaCenterIn (T : Subgroup G) ⊓ centralizer (B : Set G)
  let H := B ⊔ (T : Subgroup G)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le
    (show F ≤ omegaCenterIn (T : Subgroup G) from inf_le_left)
  have hFH : F ≤ H := fun x hx => mem_sup_right ((mem_omegaCenterIn_iff _ _).mp hx.1).1
  have hFC : F ≤ centralizer (H : Set G) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx.1).2.1))
  have hFQ : F ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 F) hFH
      ((le_centralizer_iff.mp hFC).trans (Subgroup.centralizer_le_normalizer _))
  intro x hx
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨hFQ hx,centralizer_le (pCoreIn_le 2 H) (hFC hx),
      ((mem_omegaCenterIn_iff _ _).mp hx.1).2.2⟩

end Setup.NaturalCoordinates
namespace SylowNormalizer.Points
variable {E : S.NaturalCoordinates} (P : Points E)

/-- The actual point-residual omega center reduces to a fixed space in the
original V; no separate splitting hypothesis is needed. -/
theorem five_core_omega_reduction_of_weight_six
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn ((P.five ⊔ (T : Subgroup G)).pCoreIn 2) =
      (V ⊓ centralizer ((P.five ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) ⊔ P.fixed ∧
    Disjoint (V ⊓ centralizer ((P.five ⊔ (T : Subgroup G)).pCoreIn 2 : Set G))
      P.fixed :=
  E.subjoin_core_omega_decomposition_of_weight_six structural escape hsix P.five
    ((pointResidual_le L (P.two : G)).trans inf_le_left)

/-- The fixed factor in the literal source decomposition is in the
original point-residual core omega center. -/
theorem five_sylow_fixed_le_core_omega :
    omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G) ≤
      omegaCenterIn ((P.five ⊔ (T : Subgroup G)).pCoreIn 2) :=
  Setup.NaturalCoordinates.sylow_fixed_le_subjoin_omega P.five

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
