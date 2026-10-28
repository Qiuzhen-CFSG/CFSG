module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PanelRadical
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RootIntervals
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.LinearCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiRootLayers

/-!
# The mixed Omega bounds (6.2) and (6.3) on the source quotient

Natural faithful-panel markings discharge (2B) for the linear and Suzuki
endpoints, including parameter zero. The short-interval commutator theorem
then bounds each same-type mixed commutator by the intervening root.
Adjacent-root commutation and the elementary linear root force (6.2).
Every element of the actual Suzuki Omega is a square; applying the square
commutator identity with the same elementary intervening root gives both
assertions of (6.3).

Source: Fong--Seitz I (1973), proof of (6H), equations (6.2)--(6.3),
printed p.52, checked against the PDF. These are containment and vanishing
assertions. The later nonzero commutator equality is not asserted here.
The two root fields need not yet be synchronized. Constructing the natural
rank-one markings, the remaining (6H) clauses and the compatible Section 10
coordinates remains part of the source reconstruction. OriginalMixedBounds
retains the actual original endpoint and generated-carrier representatives.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include μ hB in
theorem marked_suzuki_remainder_le_kernel :
    simpleRemainder Q split i ≤ localKernel Q i := by
  apply remainder_le_panelKernel_of_marking Q split i μ (matrixRootSylow m)
    (by
      change (quotientBorel Q i).map μ.toMonoidHom =
        normalizer ((matrixRootSylow m : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m))
      rw [matrixRootSylow_carrier]
      exact hB)
    (suzuki_normalizer_index m (matrixRootSylow m))

include ν hC in
theorem marked_linear_remainder_le_kernel :
    simpleRemainder Q split j ≤ localKernel Q j :=
  remainder_le_panelKernel_of_marking Q split j ν T hC (linear_normalizer_index T)

include ν hC in
private theorem linear_rootAt_square (w : Weyl Q)
    (x : X ⧸ Q.D) (hx : x ∈ rootAt Q split j w) : x^2 = 1 := by
  let e : rootAt Q split j w ≃* Multiplicative F :=
    (RootAction.conjugateEquiv (simpleRoot Q split j) (representative w)).trans
      (linearRootEquiv Q split j ν T hC)
  have hs : (⟨x,hx⟩ : rootAt Q split j w)^2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    change 2 • (e ⟨x,hx⟩).toAdd = 0
    rw [two_nsmul, CharTwo.add_self_eq_zero]
  exact congrArg Subtype.val hs

include μ hB ν hC in
/-- Both assertions of Fong--Seitz I (6.3), including Sz(2). The two
natural rank-one markings suffice; field synchronization is not assumed. -/
theorem source_six_three (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    ⁅simpleRoot Q split i, rootAt Q split i (Q.simple j*Q.simple i)⁆ ≤
        rootAt Q split j (Q.simple i) ∧
      ⁅omegaOneAmbient (simpleRoot Q split i),
        rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
  have hKi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  have hKj := marked_linear_remainder_le_kernel Q split j ν T hC
  have hbound := distance_two_commutator_le Q split hm i j hij hKi
  have hadj := adjacent_commutator_eq_bot Q split hm i j hij hKi hKj
  refine ⟨hbound, ?_⟩
  apply eq_bot_iff.mpr
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨z,hz,rfl⟩ := (suzukiOmega_mem_iff_square Q split i m μ hB x).mp hx
  have hb := hbound (commutator_mem_commutator hz hy)
  have hc : Commute z ⁅z,y⁆ :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hadj hz) _ hb).symm
  have htwo := linear_rootAt_square Q split j ν T hC (Q.simple i) ⁅z,y⁆ hb
  rw [mem_bot, pow_two, commutatorElement_mul_left_eq_conj_mul, hc.eq,
    mul_inv_cancel_right, ← pow_two, htwo]


include μ hB ν hC in
/-- Fong--Seitz I (6.2): the linear/linear mixed commutators lie in the
Omega of the intervening Suzuki root. Adjacent-root commutation makes
each element commutator a square-trivial element of that root. -/
theorem source_six_two (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    ⁅simpleRoot Q split j, rootAt Q split j (Q.simple i*Q.simple j)⁆ ≤
      omegaOneAmbient (rootAt Q split i (Q.simple j)) := by
  have hKi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  have hKj := marked_linear_remainder_le_kernel Q split j ν T hC
  have hbound := distance_two_commutator_le Q split hm j i hij.symm hKj
  have hadj := adjacent_commutator_eq_bot Q split hm j i hij.symm hKj hKi
  apply commutator_le.mpr
  intro x hx y hy
  have hb := hbound (commutator_mem_commutator hx hy)
  have hc : Commute x ⁅x,y⁆ :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hadj hx) _ hb).symm
  have hx2 := linear_rootAt_square Q split j ν T hC 1 x
    (by simpa only [rootAt_one] using hx)
  have htwo : ⁅x,y⁆^2 = 1 := by
    calc
      ⁅x,y⁆^2 = ⁅x^2,y⁆ := by
        rw [pow_two x, commutatorElement_mul_left_eq_conj_mul, hc.eq,
          mul_inv_cancel_right, pow_two]
      _ = 1 := by rw [hx2, commutatorElement_one_left]
  exact (omegaOneAmbient_le_iff _ _).mp le_rfl _ hb htwo

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
