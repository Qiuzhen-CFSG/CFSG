module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceSubgroups
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersThompsonSourceSplitting
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction

/-!
# LocalAnalysisCentralizersThompsonSourceSubgroups at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersThompsonSourceSubgroups`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
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

include S in

theorem subjoin_core_center_le_core_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (B : Subgroup G) (hBL : B ≤ L) :
    centerIn ((B ⊔ (T : Subgroup G)).pCoreIn 2) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hVQ : V ≤ (B ⊔ (T : Subgroup G)).pCoreIn 2 :=
    S.chosen.le_core.trans (core_le_subjoin_core B hBL)
  rw [← RecognitionSource.chosen_sylow_centralizer_eq_core_at S.hypothesis S.chosen structural]
  exact le_inf (inf_le_left.trans (subjoin_core_le_sylow B))
    (inf_le_right.trans (centralizer_le hVQ))

include S in

theorem subjoin_core_omega_eq_inf_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (B : Subgroup G) (hBL : B ≤ L) :
    omegaCenterIn ((B ⊔ (T : Subgroup G)).pCoreIn 2) =
      omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓
        centralizer ((B ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
  omegaCenterIn_eq_inf_of_center_le _ _ (core_le_subjoin_core B hBL)
    (subjoin_core_center_le_core_at (S := S) structural B hBL)

include S in

theorem sylow_component_fixed_le_subjoin_omega_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (B : Subgroup G) (hBL : B ≤ L) :
    omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      omegaCenterIn ((B ⊔ (T : Subgroup G)).pCoreIn 2) := by
  intro c hc
  have hcz := (mem_omegaCenterIn_iff _ _).mp hc.1
  have hcQ : c ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← RecognitionSource.chosen_sylow_centralizer_eq_core_at S.hypothesis S.chosen structural]
    exact ⟨hcz.1,centralizer_le S.chosen.le_component hc.2⟩
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨core_le_subjoin_core B hBL hcQ,
      centralizer_le (subjoin_core_le_sylow B) hcz.2.1,hcz.2.2⟩

theorem subjoin_core_omega_decomposition_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  have hCU : C ≤ U := sylow_component_fixed_le_subjoin_omega_at (S := S) structural B hBL
  have hVU : V ⊓ centralizer ((B ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ U := by
    intro v hv
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨core_le_subjoin_core B hBL (S.chosen.le_core hv.1),hv.2,
        ((mem_omegaCenterIn_iff _ _).mp (chosen_le_core_omega (S := S) hv.1)).2.2⟩
  refine ⟨le_antisymm ?_ (sup_le hVU hCU),E.core_omega_factors_disjoint.mono_left inf_le_left⟩
  intro x hx
  have hx' : x ∈ V ⊔ C := by
    rw [← (E.core_omega_decomposition_of_weight_six_at structural escape hsix).1]
    exact (subjoin_core_omega_eq_inf_at (S := S) structural B hBL ▸ hx).1
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

end Setup.NaturalCoordinates

namespace SylowNormalizer.Points

variable {E : S.NaturalCoordinates} (P : Points E)

theorem five_core_omega_reduction_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn ((P.five ⊔ (T : Subgroup G)).pCoreIn 2) =
      (V ⊓ centralizer ((P.five ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) ⊔ P.fixed ∧
    Disjoint (V ⊓ centralizer ((P.five ⊔ (T : Subgroup G)).pCoreIn 2 : Set G))
      P.fixed :=
  E.subjoin_core_omega_decomposition_of_weight_six_at structural escape hsix P.five
    ((pointResidual_le L (P.two : G)).trans inf_le_left)

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

