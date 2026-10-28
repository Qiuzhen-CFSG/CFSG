module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiOmega
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions
public import Theory.SpecificGroups.Suzuki.OddCartan
public import Theory.Frattini.SquareImage

/-!
# The actual Suzuki root Frattini quotient has order q

The source first-coordinate homomorphism has elementary abelian image of
order q, so kills the Frattini subgroup and supplies the lower bound. The
naturally marked matrix-root equivalence transfers the independent upper
bound coming from squares in the root center. Conjugation gives the same
order for every literal source root conjugate.

Source: Fong--Seitz I (1973), (6H)(a), p.51. This positive-parameter lemma
feeds SuzukiActions; parameter zero is handled there by its trivial odd
Cartan image, without using a positive-parameter structure theorem.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure (rootAt)
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include μ hB in
theorem suzuki_simple_frattini_card (hm : 0 < m) :
    Nat.card (simpleRoot Q split i ⧸ frattini (simpleRoot Q split i)) = 2^(2*m+1) := by
  let f := suzukiFirstCoordinate Q split i m μ hB
  have hphi : frattini (simpleRoot Q split i) ≤ f.ker := by
    apply Theory.GroupTheory.frattini_le_ker_of_square_image
    intro a
    change 2 • (f a).toAdd = 0
    exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)
  have hlo := Nat.card_le_card_of_surjective
    (QuotientGroup.lift _ f hphi)
    (QuotientGroup.lift_surjective_of_surjective _ f
      (suzukiFirstCoordinate_surjective Q split i m μ hB) hphi)
  have hfield : Nat.card (Multiplicative (BinaryGaloisField (2*m+1))) = 2^(2*m+1) :=
    (Nat.card_congr Multiplicative.ofAdd.symm).trans (GaloisField.card 2 (2*m+1) (by omega))
  rw [hfield] at hlo
  apply le_antisymm ?_ hlo
  rw [Nat.card_congr (QuotientGroup.congr _ _ (suzukiRootEquiv Q split i m μ hB)
    (frattini_map_equiv _)).toEquiv]
  exact SuzukiCartan.root_frattini_quotient_card_le m hm

include μ hB in
theorem suzuki_rootAt_frattini_card (hm : 0 < m) (w : Weyl Q) :
    Nat.card (rootAt Q split i w ⧸ frattini (rootAt Q split i w)) = 2^(2*m+1) := by
  unfold HexagonStructure.rootAt
  rw [Nat.card_congr (QuotientGroup.congr _ _
    (RootAction.conjugateEquiv (simpleRoot Q split i) (representative w))
    (frattini_map_equiv _)).toEquiv]
  exact suzuki_simple_frattini_card Q split i m μ hB hm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
