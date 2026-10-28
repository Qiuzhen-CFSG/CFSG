module
public import Theory.Representation.BinaryLinearRecognition
public import Theory.Representation.FullLinearSelfDual

/-!
# Excluding the natural binary linear degree by self-duality

A faithful PSL_n(2) representation of degree n fills GL_n(2) by equality
of orders. In dimension at least three, full GL preserves no nondegenerate
bilinear pairing, so such an action cannot be self-dual.

Source application: Aschbacher–Smith G.11.6(6), printed pp.365–366.
-/

public noncomputable section
open Representation
open scoped MatrixGroups
namespace Representation.BinaryLinearRecognition
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A faithful self-dual PSL_n(2) action cannot have natural degree n≥3. -/
theorem not_natural_degree_of_selfDual
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hs : Nonempty (ρ.Equiv ρ.dual))
    {n : ℕ} (hn : 3 ≤ n) (e : D ≃* PSL(n, ZMod 2))
    (hd : Module.finrank (ZMod 2) V = n) : False := by
  let f : V ≃ₗ[ZMod 2] _root_.BinaryLinear.OuterCyclic.Space n :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let E : (V →ₗ[ZMod 2] V)ˣ ≃* _root_.BinaryLinear.OuterCyclic.LinearGroup n :=
    (Units.mapEquiv f.conjRingEquiv.toMulEquiv).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
        (_root_.BinaryLinear.OuterCyclic.Space n))
  have hc : Nat.card (V →ₗ[ZMod 2] V)ˣ = Nat.card D :=
    (Nat.card_congr E.toEquiv).trans
      (Nat.card_congr (e.trans (_root_.BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega))).toEquiv).symm
  let : Finite (V →ₗ[ZMod 2] V)ˣ := Finite.of_equiv D
    ((e.trans (_root_.BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega))).trans E.symm).toEquiv
  have hi : Function.Injective ρ.asGroupHom := fun x y h => hf (congrArg Units.val h)
  exact binary_not_surjective_of_selfDual ρ (by omega) (Classical.choice hs)
    (hi.bijective_of_nat_card_le hc.le).2
end Representation.BinaryLinearRecognition
