module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryLocalCore
public import CFSG.Quasithin.ChapterC.Section02.NormalCoreSetup

/-!
# Pushing-up hypotheses for the original paired-plane core

The residual L₀=O²(C_L(U)) is normal in H∩N_G(L). Its product with the
original Sylow T₀ has two-core Q. The existing normal-core setup theorem,
applied to these literal subgroups and the full characteristic-normalizer
control of Q, makes Q radical in H and Sylow in its normal closure inside
H∩N_G(L). No quotient image is substituted for Q.

NonFFSourceDoubledBinaryOmega supplies all these inputs for the actual
chosen-module minimal escaping group.
Source: Aschbacher–Smith 7.7.7 and C.2.3, printed pp.707 and144,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPushingUp
open DoubledBinaryLocalCore

/-- The original local residual is normal in H∩N_G(L), since H centralizes
the plane. Relative normality is used throughout. -/
theorem localResidual_normalizes
    {G : Type*} [Group G] (L U H : Subgroup G)
    (hHC : H ≤ centralizer (U : Set G)) :
    H ⊓ normalizer (L : Set G) ≤ normalizer (localResidual L U : Set G) := by
  exact ((le_inf inf_le_right
    (inf_le_left.trans (hHC.trans (centralizer (U : Set G)).le_normalizer))).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

/-- Source 7.7.7: the full original core Q satisfies C.2.3 inside H,
with normal closure taken in the literal intersection H∩N_G(L). -/
theorem pairedPlane_pushingUp
    {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    (L U T H Q : Subgroup G) (P : Sylow 2 H)
    (hH : IsSQTK κ H) (hTM : T ≤ normalizer (L : Set G))
    (hBH : localBase L T U ≤ H) (hHC : H ≤ centralizer (U : Set G))
    (hP : (P : Subgroup H).map H.subtype = T ⊓ centralizer (U : Set G))
    (hQ : (localBase L T U).pCoreIn 2 = Q) (hQne : Q ≠ ⊥)
    (hctl : Q.characteristicNormalizerClosure ≤ normalizer (L : Set G)) :
    Chapter1.RadicalExclusions.PushingUpSetup κ H Q (H ⊓ normalizer (L : Set G)) := by
  have hQH : Q ≤ H := hQ.symm.le.trans ((pCoreIn_le 2 _).trans hBH)
  apply ChapterC.pushingUpSetup_of_normal_core P hH
    (le_inf (le_sup_left.trans hBH) ((map_subtype_le _).trans (inf_le_left.trans L.le_normalizer)))
    inf_le_left (localResidual_normalizes L U H hHC)
    (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G)))
    (le_inf (map_subtype_le _) (hP.trans_le (inf_le_left.trans hTM)))
    ?_ hQne ?_
  · rw [hP]
    exact hQ.symm
  · have hh := characteristicNormalizerClosure_subgroupOf_le hQH hctl
    intro x hx
    exact ⟨x.property,hh hx⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPushingUp
