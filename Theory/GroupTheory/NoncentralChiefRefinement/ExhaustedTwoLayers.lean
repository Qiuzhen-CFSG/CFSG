module
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Comparison

/-!
# A two-factor budget exhausts two separated moved layers

Let W ≤ Q ≤ R be normal subgroups of a finite group H, with R a two-group.
If O²(H) moves W and moves R/Q, these two intervals consume two noncentral
binary chief factors. A budget of two in O²(H) therefore leaves no factor
in Q/W. The residual commutator on Q lies in W, even when Q/W is not
elementary abelian. The proof refines the literal three intervals and uses
the proved residual restriction comparison before applying commutator
idempotence to the zero-count middle interval.

Source application: Aschbacher--Smith 13.3.14, final paragraph on p.893,
with H=L₊T, W=W_K, Q=O₂(KL₊T), and R=O₂(L₊T).
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H]

/-- Movement in two separated normal layers exhausts a budget of two and
forces the residual action on the intervening layer to be trivial. -/
theorem residual_commutator_le_of_two_used_layers
    (W Q R : NormalNode H) (hWQ : W ≤ Q) (hQR : Q ≤ R)
    (hR : IsPGroup 2 R.val)
    (hW : ⁅W.val, pResidual 2 H⁆ ≠ ⊥)
    (hupper : ¬ ⁅R.val, pResidual 2 H⁆ ≤ Q.val)
    (hcount : ∀ s : ChiefSeries (pResidual 2 H),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2) :
    ⁅Q.val, pResidual 2 H⁆ ≤ W.val := by
  obtain ⟨a,ha0,haW⟩ := exists_chiefSeries (⊥ : NormalNode H) W bot_le
  obtain ⟨b,hbW,hbQ⟩ := exists_chiefSeries W Q hWQ
  obtain ⟨c,hcQ,hcR⟩ := exists_chiefSeries Q R hQR
  obtain ⟨d,hdR,hd1⟩ := exists_chiefSeries R (⊤ : NormalNode H) le_top
  have ha : a.noncentralTwoCount ≠ 0 := by
    intro hz
    have hp : IsPGroup 2 a.last.val := by
      rw [haW]
      exact hR.to_le (hWQ.trans hQR)
    have hh := a.residual_commutator_le_head_of_count_zero hp hz
    rw [haW,ha0] at hh
    exact hW (le_bot_iff.mp hh)
  have hc : c.noncentralTwoCount ≠ 0 := by
    intro hz
    have hp : IsPGroup 2 c.last.val := by rwa [hcR]
    have hh := c.residual_commutator_le_head_of_count_zero hp hz
    rw [hcR,hcQ] at hh
    exact hupper hh
  let ab := a.smash b (haW.trans hbW.symm)
  let abc := ab.smash c ((RelSeries.last_smash _).trans (hbQ.trans hcQ.symm))
  let s := abc.smash d ((RelSeries.last_smash _).trans (hcR.trans hdR.symm))
  have hs0 : s.head = ⊥ := by simp only [s,abc,ab,RelSeries.head_smash,ha0]
  have hs1 : s.last = ⊤ := by simp only [s,RelSeries.last_smash,hd1]
  obtain ⟨t,ι,hi,hi0,hi1,ht0,ht1,hst⟩ :=
    ChiefSeries.exists_complete_pResidual_refinement s hs0 hs1
  have htotal : a.noncentralTwoCount + b.noncentralTwoCount +
      c.noncentralTwoCount + d.noncentralTwoCount ≤ 2 := by
    have hb := hst.trans (hcount t ht0 ht1)
    simpa only [s,abc,ab,ChiefSeries.noncentralTwoCount_smash] using hb
  have hb : b.noncentralTwoCount = 0 := by omega
  have hp : IsPGroup 2 b.last.val := by rw [hbQ]; exact hR.to_le hQR
  have hh := b.residual_commutator_le_head_of_count_zero hp hb
  simpa only [hbW,hbQ] using hh
end NoncentralChiefRefinement
