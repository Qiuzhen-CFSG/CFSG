module
public import CFSG.Quasithin.ChapterG.Section03.Recognition
public import CFSG.Quasithin.ChapterG.Section03.Decomposition
public import Mathlib.GroupTheory.Schreier

/-!
# A fixed sum of two transvection centers

In a binary action with trivial two-core, an orbit with root groups of order
at least four has the corrected G.3.1 block decomposition. If two points of
that orbit have a fixed sum, either they lie in one block and the sum is
zero, or one block moves its point while fixing the other, a contradiction.
Only the two points need lie in the orbit; no spanning hypothesis is needed.

The cardinality-to-rank bridge uses the actual quotient by the two-core.
Source: Aschbacher--Smith G.3.1, printed pp.337--338, applied in 10.2.11(3),
printed p.754. The corrected recognition's two-core guard is retained.
-/

@[expose] public noncomputable section

open Subgroup BinaryLinear BinaryTransvectionGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction
open ChapterG.Section03

theorem fixed_sum_eq_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {H : Subgroup (BinaryLinear.GL W)} [Finite H] {Δ : Set W}
    (h : Hypotheses H Δ) (hcore : pCore 2 H = ⊥)
    {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hfix : ∀ g ∈ H, g (x+y) = x+y) : x+y=0 := by
  have hf := fullAction_of_hypotheses_of_twoCore_eq_bot h hcore
  let i : OrbitBlock H Δ := ⟨MulAction.orbit (generated H Δ) x, x, hx, rfl⟩
  let j : OrbitBlock H Δ := ⟨MulAction.orbit (generated H Δ) y, y, hy, rfl⟩
  have hxi : x ∈ blockSpace H Δ i := Submodule.subset_span (MulAction.mem_orbit_self x)
  have hyj : y ∈ blockSpace H Δ j := Submodule.subset_span (MulAction.mem_orbit_self y)
  by_cases hij : i = j
  · have hxy : x+y ∈ blockSpace H Δ i :=
      Submodule.add_mem _ hxi (hij.symm ▸ hyj)
    exact congrArg Subtype.val (DecompositionProof.block_fixed_zero hf i ⟨x+y,hxy⟩
      (fun g hg => hfix g (generated_le H i.val hg)))
  · have hz := DecompositionProof.block_fixed_zero hf i ⟨x,hxi⟩ (by
      intro g hg
      have hh := hfix g (generated_le H i.val hg)
      rw [map_add, DecompositionProof.blocks_cross_fix h hij g hg y hyj] at hh
      exact add_right_cancel hh)
    exact (h.nonzero x hx (congrArg Subtype.val hz)).elim

theorem root_hypotheses_of_card {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {H : Subgroup (BinaryLinear.GL W)} [Finite H] {x : W}
    (hx : x ≠ 0) (hcore : pCore 2 H = ⊥) (hc : 2 < Nat.card (rootGroup H x)) :
    Hypotheses H (MulAction.orbit H x) := by
  refine ⟨?_, ⟨x,rfl⟩, ?_⟩
  · rintro y ⟨g, rfl⟩
    exact fun he => hx (g.val.injective (he.trans (g.val.map_zero).symm))
  · intro y hy
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hy
    change 1 < Group.rank (rootQuotientImage H (g.val x))
    have hr : 2 < Nat.card (rootGroup H (g.val x)) := by
      have heq : Nat.card (rootGroup H (g.val x)) = Nat.card (rootGroup H x) := by
        rw [← rootGroup_conjugate g.property x]
        exact (Nat.card_congr ((MulAut.conj g.val).subgroupMap (rootGroup H x)).toEquiv).symm
      rwa [heq]
    let q := QuotientGroup.mk' (pCore 2 H)
    have hi : Function.Injective q := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk', hcore]
    have hcq : Nat.card (rootQuotientImage H (g.val x)) =
        Nat.card (rootGroup H (g.val x)) := by
      exact (Nat.card_congr (((rootGroup H (g.val x)).subgroupOf H).equivMapOfInjective q hi).toEquiv).symm.trans
        (Nat.card_congr (subgroupOfEquivOfLe (rootGroup_le H (g.val x))).toEquiv)
    let : IsElementaryAbelian 2 (rootQuotientImage H (g.val x)) :=
      rootQuotientImage_elementaryAbelian H (g.val x)
    have hbound : Nat.card (rootQuotientImage H (g.val x)) ≤
        2 ^ Group.rank (rootQuotientImage H (g.val x)) := by
      exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' _
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _)))
    by_contra hn
    have hp := pow_le_pow_right' (by decide : 1 ≤ (2:ℕ)) (not_lt.mp hn)
    rw [hcq] at hbound
    omega

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction
