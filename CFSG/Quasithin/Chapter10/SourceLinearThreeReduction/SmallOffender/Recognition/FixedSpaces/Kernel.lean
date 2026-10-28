module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Quotient

/-!
# Faithfulness of the original moved central quotient

The kernel of L on W/C_W(L) is normal in L and contains O₂(L), which
centralizes the full module. Simplicity of the actual quotient leaves only
two possibilities. The whole-component kernel would imply W≤C_G(L),
contrary to W=[W,L]≠1. Hence the kernel is exactly the original two-core.
This proves the component-kernel input without any module-model marking.
Source: Aschbacher--Smith 10.1.1 and the kernel step of 10.2.12, pp.741,754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual component kernel is O₂(L), independent of its module model. -/
theorem moved_quotient_kernel
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    commutatorPreimage L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) = L.pCoreIn 2 := by
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (L : Set G)
  let K := commutatorPreimage L W Z
  let N := K.subgroupOf L
  have hLW : L ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
  have hLZ : L ≤ normalizer (Z : Set G) :=
    (le_inf L.le_normalizer hLW).trans (source_original_moved_fixed_normalizer D)
  have hLK : L ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized L W Z L hLZ L.le_normalizer hLW hLZ
  let : N.Normal := normal_subgroupOf_of_le_normalizer hLK
  have hKL : K ≤ L := commutatorPreimage_le _ _ _
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hcoreK : L.pCoreIn 2 ≤ K := by
    apply le_commutatorPreimage (pCoreIn_le 2 L)
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      ((source_component_core_centralizes_fullModule D).trans (centralizer_le hWV))).le.trans bot_le
  have hcoreN : pCore 2 L ≤ N := by
    intro x hx
    exact hcoreK (mem_map_of_mem L.subtype hx)
  have hNne : N ≠ ⊤ := by
    intro he
    have hLK' : L ≤ K := subgroupOf_eq_top.mp he
    have hgen : ⁅W,L⁆ = W := source_full_moved_eq_commutator D
    have hWC : W ≤ centralizer (L : Set G) := by
      rw [←hgen,commutator_comm]
      exact ((commutator_mono hLK' le_rfl).trans
        (commutator_commutatorPreimage_le L W Z hLZ)).trans inf_le_right
    have hzero := commutator_eq_bot_iff_le_centralizer.mpr hWC
    rw [hgen] at hzero
    exact source_full_moved_ne_bot D hzero
  let f := QuotientGroup.mk' (pCore 2 L)
  let := quotient_simple D hn
  have hmapnormal : (N.map f).Normal :=
    Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
  rcases hmapnormal.eq_bot_or_eq_top with he | he
  · have hNc : N ≤ pCore 2 L := by
      have hh := (map_eq_bot_iff (f := f) N).mp he
      simpa only [f,QuotientGroup.ker_mk'] using hh
    have heN : N = pCore 2 L := le_antisymm hNc hcoreN
    have hh := congrArg (map L.subtype) heN
    rw [map_subgroupOf_eq_of_le hKL] at hh
    exact hh
  · have htop : N = ⊤ := by
      have hh := congrArg (comap f) he
      rw [comap_map_eq,comap_top,show f.ker = pCore 2 L from QuotientGroup.ker_mk' _,
        sup_eq_left.mpr hcoreN] at hh
      exact hh
    exact (hNne htop).elim

/-- The only remaining action input is a nonfixed involution-fixed vector. -/
theorem actionInputs_of_nonfixed
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (c : Context D)
    (hfixed : ∀ b ∈ D.maximalLocal,
      b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) → b ^ 2 = 1 →
      ¬ ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer (L : Set G)) :
    ActionInputs D :=
  actionInputs_of_kernel_and_nonfixed D c (moved_quotient_kernel D c.nonnormal) hfixed

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
