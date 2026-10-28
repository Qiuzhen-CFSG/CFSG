module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Kernel
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# An involution fixes a vector outside the component-fixed part

An involution on an elementary abelian two-group fixes its displacement.
Thus if C_W(b) were contained in C_W(L), b would act trivially on W/C_W(L).
The component-kernel theorem and the three-subgroups lemma then force b to
centralize W, contradicting W=[W,L]≠1. The literal two-factor action supplies
normalization of L from b∈N_M(W). No module classification is needed.

This discharges the sentence following (*) in Aschbacher--Smith 10.2.12,
printed p.754, directly from the original group-action hypotheses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Every original stabilizing involution fixes a non-component-fixed vector. -/
theorem involution_fixed_not_le
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (c : Context D)
    (b : G) (hbM : b ∈ D.maximalLocal)
    (hbN : b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hb2 : b ^ 2 = 1) :
    ¬ ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer (L : Set G) := by
  intro hfixed
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (L : Set G)
  let H := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  let := source_full_moved_elementary D
  have hinv : ∀ w ∈ W, w⁻¹ = w := by
    intro w hw
    exact inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw))
  have hs : b*b = 1 := by simpa only [pow_two] using hb2
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  have hbL := source_original_moved_stabilizer_le_component_normalizer D ht htn
    (c.crossed t ht htn) ⟨hbM,hbN⟩
  have hHZ : H ≤ normalizer (Z : Set G) := source_original_moved_fixed_normalizer D
  have hdisp : ∀ w ∈ W, ⁅b,w⁆ ∈ Z := by
    intro w hw
    have hbw : b*w*b⁻¹ ∈ W := (mem_normalizer_iff.mp hbN w).mp hw
    have hd : ⁅b,w⁆ ∈ W := W.mul_mem hbw (W.inv_mem hw)
    have he : b*⁅b,w⁆*b⁻¹ = ⁅b,w⁆ := by
      change b*(b*w*b⁻¹*w⁻¹)*b⁻¹ = b*w*b⁻¹*w⁻¹
      calc
        _ = (b*b)*w*(b*b)⁻¹ * (b*w*b⁻¹)⁻¹ := by group
        _ = w*(b*w*b⁻¹) := by simp only [hs,one_mul,inv_one,mul_one,hinv _ hbw]
        _ = (b*w*b⁻¹)*w := setLike_mul_comm hw hbw
        _ = _ := by rw [hinv w hw]
    exact ⟨hd,hfixed ⟨hd,mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm⟩⟩
  have hbK : b ∈ commutatorPreimage H W Z :=
    (mem_commutatorPreimage_iff H W Z hHZ b).mpr ⟨⟨hbL,hbN⟩,hdisp⟩
  have hker : commutatorPreimage L W Z ≤ centralizer (W : Set G) := by
    rw [moved_quotient_kernel D c.nonnormal]
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact (source_component_core_centralizes_fullModule D).trans (centralizer_le hWV)
  have hbC := commutatorPreimage_le_centralizer_of_fully_moved H L W Z
    (le_inf L.le_normalizer (normalizer_commutator_ge_right _ _))
    inf_le_left inf_le_right hHZ inf_le_right (source_full_moved_eq_commutator D) hker hbK
  have hWC : W ≤ centralizer ({b} : Set G) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (hbC w hw)
  have hzero := commutator_eq_bot_iff_le_centralizer.mpr
    ((le_inf le_rfl hWC).trans hfixed)
  rw [source_full_moved_eq_commutator D] at hzero
  exact source_full_moved_ne_bot D hzero

/-- The entire original component-action obligation is now discharged. -/
theorem source_actionsAt : ActionsAt (G := G) T := by
  intro L D c _ b hbM hbN hb2
  exact involution_fixed_not_le D c b hbM hbN hb2

/-- All action inputs used in the supplement proof, with no extra premises. -/
theorem source_actionInputs
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (c : Context D) :
    ActionInputs D :=
  actionInputs_of_nonfixed D c (involution_fixed_not_le D c)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
