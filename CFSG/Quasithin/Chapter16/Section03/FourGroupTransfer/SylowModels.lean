module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Reduction

/-!
# Assembly of the five Sylow geometries in 16.3.4

The common construction is proved in `Reduction`. This module keeps the
five concrete calculations explicit until they are established. The pair
list and centerlessness are earlier-table inputs; the five center embeddings
and strict Sylow-order comparisons are additional model obligations.

The theorem below is a conditional assembly, not a proof of 16.3.4. The
source owner must discharge the earlier tables, and the concrete model
workers must discharge each of the five calculation premises.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.4, printed p.1178 / PDF p.1195.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup Theory.GroupTheory ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z t i : G} {L K : Subgroup G}

/-- Assemble the exact geometry from the earlier pair table and the five
intrinsic calculations. Every extra premise remains explicit. -/
theorem geometry_of_pair_calculations
    (h : ExclusionSetup T z L K t i)
    (heven : Even (Nat.card L)) (hZ : center L = ⊥)
    (pairs : ExcludedPairModels L K)
    (unitary : ∀ n : ℕ, 2 ≤ n → ClassicalGroup.IsPSU K 3 (2 ^ n) →
      ClassicalGroup.IsPSL L 2 (2 ^ n) → FullSylowCenterLifting L K ∧ SylowOrderGap L K)
    (m12 : Nonempty (K ≃* SporadicName.m12.Carrier) →
      Nonempty (L ≃* alternatingGroup (Fin 5)) →
      InvolutionCenterLifting L K ∧ SylowOrderGap L K)
    (j2 : Nonempty (K ≃* SporadicName.j2.Carrier) →
      (Nonempty (L ≃* alternatingGroup (Fin 5)) ∨ ClassicalGroup.IsPSL L 3 2) →
      InvolutionCenterLifting L K ∧ SylowOrderGap L K)
    (hs : Nonempty (K ≃* SporadicName.hs.Carrier) →
      (Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (L ≃* alternatingGroup (Fin 8))) →
      InvolutionCenterLifting L K ∧ SylowOrderGap L K)
    (ru : Nonempty (K ≃* SporadicName.ru.Carrier) →
      Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) →
      InvolutionCenterLifting L K ∧ SylowOrderGap L K) :
    ExcludedSylowGeometry T L K := by
  rcases pairs with ⟨n, hn, hK, hL⟩ | ⟨hK, hL⟩ | ⟨hK, hL⟩ | ⟨hK, hL⟩ | ⟨hK, hL⟩
  · obtain ⟨lift, gap⟩ := unitary n hn hK hL
    exact geometry_of_fullSylowCenterLifting h.localSetup h.normal hZ gap lift
  · obtain ⟨lift, gap⟩ := m12 hK hL
    exact geometry_of_involutionCenterLifting h.localSetup h.normal heven hZ gap lift
  · obtain ⟨lift, gap⟩ := j2 hK hL
    exact geometry_of_involutionCenterLifting h.localSetup h.normal heven hZ gap lift
  · obtain ⟨lift, gap⟩ := hs hK hL
    exact geometry_of_involutionCenterLifting h.localSetup h.normal heven hZ gap lift
  · obtain ⟨lift, gap⟩ := ru hK hL
    exact geometry_of_involutionCenterLifting h.localSetup h.normal heven hZ gap lift

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
