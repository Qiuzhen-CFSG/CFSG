module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanCyclic
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OctagonRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.LinearCoordinates
public import Theory.ElementaryAbelian.Injective

/-!
# The actual perpendicular linear root action in the Ree source

Natural linear panel coordinates identify each conjugated root with the
additive field. The full Cartan image is cyclic of order q-1 and therefore
acts regularly on its nonidentity elements. In the octagon the original
simple reflection preserves the perpendicular root. Odd binary dimension
then forces its involutory lift to centralize that root.

This proves the linear action step of Fong--Seitz I (1973), (6H)(a), p.51,
from the earlier natural rank-one marking and odd-degree restriction of
(1J). CommonField consumes it in the literal two-panel divisibility argument.
The binary field and the full source quotient are retained throughout.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure (rootAt rootAt_torus_normalizes)
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (n : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set _))

/-- Coordinates for every conjugate of the same naturally marked linear root. -/
def linearRootAtEquiv (w : Weyl Q) : rootAt Q split i w ≃* Multiplicative (BinaryGaloisField n) :=
  (RootAction.conjugateEquiv (simpleRoot Q split i) (representative w)).trans
    (linearRootEquiv Q split i μ T hB)

@[simp] theorem linearRootAtEquiv_apply (w : Weyl Q) (x : rootAt Q split i w) :
    linearRootAtEquiv Q split i n μ T hB w x =
      linearRootEquiv Q split i μ T hB
        ⟨(representative w : X ⧸ Q.D)*x*(representative w : X ⧸ Q.D)⁻¹,x.property⟩ := rfl

include μ hB in
theorem linear_rootAt_card (hn : 0 < n) (w : Weyl Q) :
    Nat.card (rootAt Q split i w) = 2^n := by
  rw [Nat.card_congr (linearRootAtEquiv Q split i n μ T hB w).toEquiv,
    Nat.card_congr Multiplicative.ofAdd.symm]
  exact GaloisField.card 2 n hn.ne'

include μ hB in
theorem linear_rootAt_elementary (w : Weyl Q) : IsElementaryAbelian 2 (rootAt Q split i w) := by
  let : IsElementaryAbelian 2 (Multiplicative (BinaryGaloisField n)) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      change 2 • x.toAdd = 0
      exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)
  }
  exact IsElementaryAbelian.of_injective (linearRootAtEquiv Q split i n μ T hB w).toMonoidHom
    (linearRootAtEquiv Q split i n μ T hB w).injective

include μ hB in
theorem linear_rootAction_cyclic (hn : 0 < n) (s : RootReflection Q split i) (w : Weyl Q) :
    IsCyclic (rootAction Q split i w).range :=
  (rootActionImageEquiv Q split i w).isCyclic.mpr
    (linear_cartanImage_cyclic Q split i n hn μ T hB s)

include μ hB in
theorem linear_rootAction_card (hn : 0 < n) (s : RootReflection Q split i) (w : Weyl Q) :
    Nat.card (rootAction Q split i w).range = 2^n-1 := by
  rw [Nat.card_congr (rootActionImageEquiv Q split i w).toEquiv]
  exact linear_cartanImage_card Q split i n hn μ T hB s

include μ hB in
/-- The actual involutory lift of s_i centralizes the perpendicular linear
root. The odd-degree input is the earlier octagon parameter restriction
(I (1J)); the source action is derived from the natural panel marking. -/
theorem linear_perpendicular_reflection_centralizes
    (hm : rotationOrder Q = 8) (hn : Odd n) (j : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split i) :
    ((involutoryRootReflection Q split i s).val : X ⧸ Q.D) ∈
      centralizer (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  let w := Q.simple j*Q.simple i*Q.simple j
  let r := involutoryRootReflection Q split i s
  let := linear_rootAt_elementary Q split i n μ T hB w
  let : IsCyclic (RootAction.action (Q.tits.B ⊓ Q.tits.N)
      (rootAt Q split i w) (rootAt_torus_normalizes Q split i w)).range :=
    linear_rootAction_cyclic Q split i n μ T hB hn.pos s w
  exact RootAction.normalizing_involution_centralizes (Q.tits.B ⊓ Q.tits.N)
    (rootAt Q split i w) (rootAt_torus_normalizes Q split i w) hn
    (linear_rootAction_card Q split i n μ T hB hn.pos s w)
    (linear_rootAt_card Q split i n μ T hB hn.pos w) r.val
    (perpendicular_root_normalizes Q split hm i j hij r.val r.class_eq)
    (torus_normalizes r.val) (involutoryRootReflection_sq Q split i s)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
