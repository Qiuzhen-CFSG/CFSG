module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.MinimalLocal
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.SmallOvergroups
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.PSL3Two.AlternatingFiveObstruction

/-!
# Minimality eliminates the binary generation alternative

An intermediate overgroup of Y₀T outside M is eligible because it contains
the nontrivial normal two-core of H. Minimality makes it equal to H. In the
binary degree-four and degree-five cases, five divides the order of the
actual component image and hence H/O₂(H). Thus such an intermediate group
cannot have quotient PSL₃(2), whose order divides 168. The S₃ × S₃ case
is already solvable and is controlled by (j).

Consequently the proved binary parabolic-generation alternative forces the
actual S₈ middle-node identification. This route needs no second local
offender construction on the smaller groups. The middle-node contradiction
remains separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed p.1145, with the minimal choice made before (h).
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

open Subgroup ModelExclusions
open Chapter2.ComponentRefinement.LieType.Binary

private theorem five_dvd_binary_card (n : ℕ) [NeZero n] (hn : n = 4 ∨ n = 5) :
    5 ∣ Nat.card (PSL n) := by
  rcases hn with rfl | rfl
  · have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
    rw [Nat.card_zmod, show 2 - 1 = 1 by decide, Nat.gcd_one_right, mul_one, mul_one] at h
    have hc : Nat.card (PSL 4) = 20160 := h.trans (by decide +kernel)
    rw [hc]
    decide
  · have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    rw [Nat.card_zmod, show 2 - 1 = 1 by decide, Nat.gcd_one_right, mul_one, mul_one] at h
    have hc : Nat.card (PSL 5) = 9999360 := h.trans (by decide +kernel)
    rw [hc]
    decide

variable {G : Type*} [Group G] [Finite G]
    {H M Y0 T upper : Subgroup G}

/-- In the selected minimal H, an order obstruction on its star quotient
already places every PSL₃(2) intermediate overgroup in M. -/
theorem MinimalLocal.binary_three_overgroup_le
    (hm : MinimalLocal Y0 T M upper H) (hQT : localTwoCore H ≤ T)
    (hfive : 5 ∣ Nat.card (H ⧸ pCore 2 H))
    (K : Subgroup G) (hbase : Y0 ⊔ T ≤ K) (hKH : K ≤ H)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    K ≤ M := by
  by_contra hout
  have he := hm.eq_of_eligible (hm.intermediate_eligible hQT hbase hKH hout) hKH
  subst K
  have hd : 5 ∣ 168 := hfive.trans
    ((Nat.card_congr e.toEquiv).symm ▸ Matrix.PSL3Two.card_PSL_dvd)
  norm_num at hd

/-- Actual consumer: binary parabolic generation, minimality and the
component order force the compatible S₈ middle-node alternative. -/
theorem middleNodeEight_of_minimal_binary {L : Subgroup G} {n : ℕ} [NeZero n]
    (hm : MinimalLocal Y0 T M upper H) (S : Sylow 2 G) (hS : (S : Subgroup G) = T)
    (d : BinaryLocalData H M L Y0 T n) :
    Nonempty (BinaryGeometry.MiddleNodeEight (starImage H L) (componentParabolic H L Y0 T)) := by
  have hc : 5 ∣ Nat.card (starImage H L) := by
    rw [Nat.card_congr d.position.model.toEquiv]
    exact five_dvd_binary_card n d.dimension
  have hfive : 5 ∣ Nat.card (H ⧸ pCore 2 H) :=
    hc.trans (card_subgroup_dvd_card (starImage H L))
  rcases BinaryGeneration.generation_or_middleNodeEight d with hg | hm8
  · apply False.elim
    apply exclude_by_small_overgroups d.reduced hg
    intro K hb hKH he
    obtain ⟨e⟩ := he
    exact hm.binary_three_overgroup_le (hm.twoCore_le_sylow S hS) hfive K hb hKH e
  · exact hm8

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
