module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.SeparatedBound
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.SpecificGroups.Suzuki.TwoRank

/-!
# The remaining quiet Suzuki configuration

A faithful binary action of Sz(2ⁿ) has degree at least 4n, whereas the
component automorphism group has two-rank at most n. The separated TI
bound would give moved order at most 2^(n+3), a contradiction for n≥3.
Thus an unmarked Suzuki small offender must move the entire full module.
Its component-fixed group is trivial. Full Thompson centralization would
supply TI and the same impossible size bound, so Thompson must move the
full module despite centralizing the original local module.

These conclusions identify the remaining case, rather than assuming its
exclusion. Quiet.FamilySelection applies them to the actual component
catalogue and the original small-offender consumer. Source:
Aschbacher--Smith 10.1.1 and 10.2.12, printed pp.741,754--755.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation BenderSuzuki.MatrixGroups
open Chapter3.Section02 ChapterE PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The unconditional faithful-degree lower bound applies to the literal moved quotient. -/
theorem suzuki_moved_card_lower_bound
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    2 ^ (4 * (2*m+1)) ≤ Nat.card (⁅D.fullModule,L⁆ : Subgroup G) := by
  let := source_full_moved_elementary D
  obtain ⟨ρ,s,hf,_⟩ := exists_moved_quotient_action D hn e
  have hd := Suzuki.finrank_ge hm ρ hf
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd
  let Q := Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅D.fullModule,L⁆)
  have hcard : Nat.card Q = 2 ^ Module.finrank (ZMod 2) Q := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [←hcard] at hp
  exact hp.trans (Nat.card_le_card_of_surjective s.coordinates s.onto)

/-- Suzuki has no separated quiet small offender, with no natural marking assumed. -/
theorem quiet_suzuki_moved_eq_full
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    ⁅D.fullModule,L⁆ = D.fullModule := by
  by_contra hn
  have hcross : ∀ {t : G}, t ∈ (T : Subgroup G) → t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
    fun ht htn => (quiet_crossed_or_moved_eq_full D c.many c.minimal hJ ht htn).resolve_right hn
  have hr : primeRank 2 (MulAut (L ⧸ pCore 2 L)) ≤ 2*m+1 := by
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact suzuki_automorphism_two_rank m hm
  have hu := quiet_moved_card_le_of_crossed_automorphism_rank D c hJ hNL hcross hr
  have hl := suzuki_moved_card_lower_bound D c.nonnormal hm e
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hl.trans hu)
  omega

/-- A quiet Suzuki small offender cannot centralize the full Thompson action. -/
theorem quiet_suzuki_full_thompson_moves
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) := by
  intro hfullJ
  have he := quiet_suzuki_moved_eq_full D c hJ hNL hm e
  have hz := quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ
  rw [he] at hz
  have hti := fullModule_ti_of_point_control D hfullJ (by
    simpa only [he] using c.pointCentralizers)
  have hr : primeRank 2 (MulAut (L ⧸ pCore 2 L)) ≤ 2*m+1 := by
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact suzuki_automorphism_two_rank m hm
  have hu := full_ti_card_le_of_automorphism_rank D c hti hz hr
  have hl := suzuki_moved_card_lower_bound D c.nonnormal hm e
  rw [he] at hl
  have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hl.trans hu)
  omega

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
