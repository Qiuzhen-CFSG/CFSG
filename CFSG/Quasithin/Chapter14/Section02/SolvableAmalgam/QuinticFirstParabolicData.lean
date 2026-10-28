module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullReeExclusion
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The original cubic partner after identification of the first Tits parabolic

First-parabolic rigidity already identifies H with Mc and YT with M,
without identification of the second parabolic. The source index five and
the concrete first order then give |T| = 2048. The original S₃ quotient
of YT gives its Sylow index three, its order 6144 and its core order 1024.
These are inputs to identification of the cubic partner, not a replacement
for its group isomorphism.

Source: Aschbacher--Smith14.2.20--21, pp.988--989; the corrected full
Tits parabolic orders are recorded in `Tits.ExceptionalParabolics.Orders`.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- All source identifications and numerical data for the cubic partner
follow from the first endpoint alone. No second-endpoint or marking input
is used. -/
theorem source_tits_first_second_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hfirst : Nonempty (Tits.ExceptionalParabolics.first ≃* H)) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    H = Mc ∧ M = X ∧ H = centralizer (centralInvolutions T : Set G) ∧
      Nat.card (T : Subgroup G) = 2048 ∧ Nat.card X = 6144 ∧
      Nat.card (pCore 2 X) = 1024 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  obtain ⟨hHMc, hMX⟩ := ReeLocal.source_ree_tits_rigidity hG T hempty hM hu hmany
    hcard e H hH (Or.inr hfirst)
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_, _, hMc, _⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  have hHcard : Nat.card H = 10240 :=
    (Nat.card_congr hfirst.some.symm.toEquiv).trans Tits.ExceptionalParabolics.first_card
  have hcount := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at hcount
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at hcount
  rw [hi, hHcard] at hcount
  have hTcard : Nat.card (T : Subgroup G) = 2048 := by omega
  obtain ⟨_, ⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hindex := SymmetricThreeTwoCore.sylow_index_three eX (T.subtype hTX)
  have hXcount := ((T : Subgroup G).subgroupOf X).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hTX).toEquiv, hTcard] at hXcount
  change ((T.subtype hTX : Sylow 2 X) : Subgroup X).index * 2048 = Nat.card X at hXcount
  rw [hindex] at hXcount
  have hXcard : Nat.card X = 6144 := by omega
  have hcore := SymmetricThreeTwoCore.card_eq eX
  change Nat.card X = 6 * Nat.card (pCore 2 X) at hcore
  rw [hXcard] at hcore
  have hQcard : Nat.card (pCore 2 X) = 1024 := by omega
  exact ⟨hHMc, hMX, hHMc.trans hMc, hTcard, hXcard, hQcard, ⟨eX⟩⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
