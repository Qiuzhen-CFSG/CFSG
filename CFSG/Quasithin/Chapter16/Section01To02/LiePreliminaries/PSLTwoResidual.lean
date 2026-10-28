module

public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.RankOne
public import Theory.SpecificGroups.PSL2.TwoResidual

/-!
# The derived endpoint for outer binary PSL₂ involutions

Transport the actual fixed-subgroup isomorphism to its two-residual, then use
O²(PSL₂(2^m)) = PSL₂(2^m)′. This includes m = 1; no perfectness or simplicity
is asserted at that endpoint. For a central cover the quotient assertion
computes the residual downstairs, separately from its surjective projection
proved in `Basic`. The full-group assertion applies to an actual PSL₂ model.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 16.1.4(4), printed p.1171. Triviality of the covering kernel from the
source (E2) hypothesis remains a multiplier/covering-group obligation.
-/

public section

namespace CFSG.Quasithin.Chapter16.LiePreliminaries
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups

private noncomputable def residualEquivDerived {H : Type*} [Group H]
    {m : ℕ} (hm : 0 < m) (e : H ≃* PSL2BinaryMatrixGroup m) :
    pResidual 2 H ≃* commutator (PSL2BinaryMatrixGroup m) :=
  (e.subgroupMap (pResidual 2 H)).trans (MulEquiv.subgroupCongr
    ((map_pResidual 2 e).trans (Theory.PSL2.binary_twoResidual_eq_commutator hm)))

/-- The two-residual of the actual fixed subgroup in a binary PSL₂ model,
retaining the derived subgroup of PSL₂(2) in the smallest case. -/
theorem psl2_outer_fixed_residual_model {L : Type*} [Group L]
    {n : ℕ} (hn : 2 ≤ n) (e : L ≃* PSL2BinaryMatrixGroup n)
    (r : MulAut L) (hr : orderOf r = 2)
    (houter : ¬ ∃ x : L, r = MulAut.conj x) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
      Nonempty (pResidual 2 r.fixedSubgroup ≃* commutator (PSL2BinaryMatrixGroup m)) := by
  let b := MulAut.congr e r
  have hb : b ^ 2 = 1 := by
    have hrpow : r ^ 2 = 1 := by simpa only [hr] using pow_orderOf_eq_one r
    change (MulAut.congr e r) ^ 2 = 1
    rw [← map_pow, hrpow, map_one]
  have hout : ¬ ∃ y, b = MulAut.conj y := fun h =>
    houter ((MulAut.congr_inner_iff e r).mp h)
  obtain ⟨g, σ, he⟩ := BenderSuzuki.ZD.Linear.binary_semilinear_coverage hn b
  obtain ⟨m, hm, hnm, ⟨d⟩⟩ :=
    BenderSuzuki.ZD.Linear.outer_fixed_model_of_semilinear hn b hb g σ he hout
  exact ⟨m, hm, hnm, ⟨residualEquivDerived hm ((MulAut.fixedSubgroupCongr e r).trans d)⟩⟩

/-- The fixed residual of the induced quotient action has the same derived
endpoint. This does not assume that fixed points lift through the center. -/
theorem psl2_quotient_outer_fixed_residual_model {L : Type*} [Group L] [Finite L]
    [IsQuasisimple L] (hodd : pPrimeCore 2 L = ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL2BinaryMatrixGroup n)
    (r : MulAut L) (hr : orderOf r = 2)
    (houter : ¬ ∃ x : L, r = MulAut.conj x) :
    let c := (centerQuotientEquivTwoCore hodd).trans e
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
      Nonempty (pResidual 2 (MulAut.centralQuotientAction c r).fixedSubgroup ≃*
        commutator (PSL2BinaryMatrixGroup m)) := by
  dsimp only
  obtain ⟨m, hm, hnm, ⟨d⟩⟩ := psl2_quotient_outer_fixed_model hodd hn e r hr houter
  exact ⟨m, hm, hnm, ⟨residualEquivDerived hm d⟩⟩

end CFSG.Quasithin.Chapter16.LiePreliminaries
