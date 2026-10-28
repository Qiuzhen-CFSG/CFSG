module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.Chart
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Theory.GroupTheory.CoordinateInversionFaithfulness

/-!
# A noncentral sign involution centralizing the four-root chart

The product h0h5 of minus-one coroots centralizes the entire signed chart.
It inverts the graph-fixed neighboring word x1(1)x4(1). If the latter word
commuted with h0h5, it would have square one; conjugating by h0 isolates
the first root parameter and forces 4=0. This is impossible in odd
characteristic. Hence the involution survives the literal central quotient.

Sources: GLS3 §§2.4 and 2.6; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.OddRankFour
open Theory.AlgebraicGroup.StandardRootSystem
open TwistedE6.FoldedSubsystem.HigherRealizations
attribute [local instance] Classical.decEq
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

namespace SixNodes
variable (c : SixNodes b) (F : Type*) [Field F] [P.IsIrreducible]

/-- The graph-stable sign involution. -/
def involution : rootGenerated P b F := c.coroot F 0 * c.coroot F 5

omit [P.IsIrreducible] in
theorem involution_square : c.involution F ^ 2 = 1 := by
  rw [involution, (c.coroot_commute F 0 5).mul_pow, coroot_square, coroot_square, mul_one]

theorem involution_chart (a : Fin 4 → Multiplicative F) :
    Commute (c.involution F) (c.chart F a) := by
  have h : c.involution F * c.chart F a * (c.involution F)⁻¹ = c.chart F a := by
    calc
      _ = c.coroot F 0 * (c.coroot F 5 * c.chart F a * (c.coroot F 5)⁻¹) * (c.coroot F 0)⁻¹ := by
        rw [involution]; group
      _ = c.chart F (corootAction F 0 (corootAction F 5 a)) := by rw [coroot_chart, coroot_chart]
      _ = _ := by
        congr 1
        funext k
        fin_cases k <;> simp [corootAction,rootIndex,typeE6CartanMatrix,Fin.ext_iff]
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem neighbor_commute (t u : F) :
    Commute (signedSimple F true (c.node 1) t) (signedSimple F true (c.node 4) u) := by
  apply signedSimple_commute _ _ _ _
    (fun h => (by decide : (1:Fin 6) ≠ 4) (c.injective h))
  rw [c.cartan]
  decide

omit [P.IsIrreducible] in
private theorem coroot_zero_neighbor (t u : F) :
    c.coroot F 0 * (signedSimple F true (c.node 1) t * signedSimple F true (c.node 4) u) *
      (c.coroot F 0)⁻¹ = signedSimple F true (c.node 1) (-t) * signedSimple F true (c.node 4) u := by
  change MulAut.conj (c.coroot F 0) (_ * _) = _
  simp only [map_mul, MulAut.conj_apply, coroot_root]
  simp [typeE6CartanMatrix,Fin.ext_iff]

omit [P.IsIrreducible] in
theorem involution_neighbor (t u : F) :
    c.involution F * (signedSimple F true (c.node 1) t * signedSimple F true (c.node 4) u) *
      (c.involution F)⁻¹ = signedSimple F true (c.node 1) (-t) * signedSimple F true (c.node 4) (-u) := by
  calc
    _ = c.coroot F 0 * (c.coroot F 5 *
        (signedSimple F true (c.node 1) t * signedSimple F true (c.node 4) u) *
        (c.coroot F 5)⁻¹) * (c.coroot F 0)⁻¹ := by rw [involution]; group
    _ = _ := by
      change MulAut.conj (c.coroot F 0) (MulAut.conj (c.coroot F 5) (_ * _)) = _
      simp only [map_mul, MulAut.conj_apply, coroot_root]
      simp [typeE6CartanMatrix,Fin.ext_iff]

omit [P.IsIrreducible] in
private theorem signed_inv (s : Bool) (i : Fin 6) (t : F) :
    signedSimple F s (c.node i) (-t) = (signedSimple F s (c.node i) t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← signedSimple_add, neg_add_cancel, signedSimple_zero]

/-- The actual graph-fixed neighboring root word does not commute with the
sign involution. No central quotient or subgroup recognition is assumed. -/
theorem involution_not_commute_neighbor (h2 : (2 : F) ≠ 0) :
    ¬ Commute (c.involution F)
      (signedSimple F true (c.node 1) 1 * signedSimple F true (c.node 4) 1) := by
  intro hc
  let x := signedSimple F true (c.node 1) (1 : F)
  let y := signedSimple F true (c.node 4) (1 : F)
  have hxy : Commute x y := c.neighbor_commute F 1 1
  have he : x⁻¹ * y⁻¹ = x * y := by
    have hh := c.involution_neighbor F 1 1
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one] at hh
    simpa only [signed_inv] using hh.symm
  have hw : (x * y) ^ 2 = 1 := by
    calc
      _ = (x * y) * (x⁻¹ * y⁻¹) := by rw [he, pow_two]
      _ = (x * y) * (y⁻¹ * x⁻¹) := congrArg (fun z => (x*y)*z) hxy.inv_inv.eq
      _ = 1 := by group
  have hw' : (x⁻¹ * y) ^ 2 = 1 := by
    have hh := congrArg (MulAut.conj (c.coroot F 0)) hw
    rw [map_pow, map_one] at hh
    have hh' : MulAut.conj (c.coroot F 0) (x * y) = x⁻¹ * y := by
      simpa only [MulAut.conj_apply, x, y, signed_inv] using c.coroot_zero_neighbor F 1 1
    rwa [hh'] at hh
  rw [hxy.mul_pow] at hw
  rw [hxy.inv_left.mul_pow] at hw'
  have hx : x ^ 4 = 1 := by
    calc
      _ = (x ^ 2 * y ^ 2) * ((x⁻¹) ^ 2 * y ^ 2)⁻¹ := by group
      _ = 1 := by rw [hw, hw']; simp
  have hfour : signedSimple F true (c.node 1) (4 : F) = 1 := by
    have hp : (4 : F) = 1 + 1 + 1 + 1 := by ring
    rw [hp, signedSimple_add, signedSimple_add, signedSimple_add]
    change x * x * x * x = 1
    simpa only [pow_succ, pow_zero, one_mul] using hx
  have hz : (4 : F) = 0 := signedSimple_injective true (c.node 1)
    (hfour.trans (signedSimple_zero F true (c.node 1)).symm)
  have hz' : (2 : F) * 2 = 0 := by simpa only [show (4 : F) = 2*2 by norm_num] using hz
  exact h2 ((mul_eq_zero.mp hz').elim id id)

theorem involution_not_mem_center (h2 : (2 : F) ≠ 0) :
    c.involution F ∉ Subgroup.center (rootGenerated P b F) := by
  intro h
  exact c.involution_not_commute_neighbor F h2
    (Subgroup.mem_center_iff.mp h _).symm

/-- The involution in the literal defining central quotient. -/
def modelInvolution : Model P b F := projection P b F (c.involution F)

theorem modelInvolution_order (h2 : (2 : F) ≠ 0) : orderOf (c.modelInvolution F) = 2 := by
  apply orderOf_eq_prime
  · rw [modelInvolution, ← map_pow, involution_square, map_one]
  · intro h
    exact c.involution_not_mem_center F h2 ((projection_eq_one_iff P b F _).mp h)

end SixNodes
end ExceptionalSplit.OddRankFour
