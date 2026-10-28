module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs

/-!
# An adjacent-node Levi factor in binary five-space

For each node, choose the other node in its outer adjacent pair. Deleting
these two cuts leaves blocks of dimensions 3+1+1 or 1+1+3. Projection onto
the three-dimensional block is an isomorphism of the diagonal group, since
binary singleton blocks have trivial automorphism groups. Composing the
actual flag diagonal quotient with this projection gives SL₃(2).
The formula on representatives retains the original geometric action.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.23, printed p.933/PDF p.950.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace BinaryLinear.SmallParabolicLevi.TwoNodes
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups

/-- Pair each node with its neighbor in the same outer pair. -/
def adjacentNode (i : Fin 4) : Fin 4 := ![1, 0, 3, 2] i

/-- The chosen pair consists of adjacent nodes. -/
theorem adjacentNode_adjacent (i : Fin 4) :
    i.val + 1 = (adjacentNode i).val ∨ (adjacentNode i).val + 1 = i.val := by
  fin_cases i <;> simp [adjacentNode]

/-- The block labels obtained by deleting the chosen two cuts. -/
noncomputable def adjacentLabel (i : Fin 4) : Fin 5 → Fin 5 :=
  cutLabel ({i, adjacentNode i} : Set (Fin 4))ᶜ

/-- Label of the unique three-dimensional diagonal block. -/
def largeBlock (i : Fin 4) : Fin 5 := if i.val < 2 then 0 else 2

private theorem univ_four : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
private theorem univ_five : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide

private theorem adjacentLabel_eq (i : Fin 4) :
    adjacentLabel i = if i.val < 2 then ![0, 0, 0, 1, 2] else ![0, 1, 2, 2, 2] := by
  fin_cases i <;> funext t <;> fin_cases t <;>
    simp [adjacentLabel, adjacentNode, cutLabel, univ_four,
      Finset.filter_insert, Finset.filter_singleton]

/-- The selected block has exactly three coordinates. -/
theorem largeBlock_card (i : Fin 4) :
    Fintype.card (Block (adjacentLabel i) (largeBlock i)) = 3 := by
  classical
  simp only [Block, Fintype.card_subtype]
  fin_cases i <;> simp [adjacentLabel_eq, largeBlock, univ_five,
    Finset.filter_insert, Finset.filter_singleton]

/-- Every other block is empty or a singleton. -/
theorem adjacent_otherBlock_card (i : Fin 4) (k : Fin 5) (hk : k ≠ largeBlock i) :
    Fintype.card (Block (adjacentLabel i) k) ≤ 1 := by
  classical
  simp only [Block, Fintype.card_subtype]
  fin_cases i <;> fin_cases k <;> simp_all [adjacentLabel_eq, largeBlock, univ_five,
    Finset.filter_insert, Finset.filter_singleton]

/-- Coordinates on the actual three-dimensional block. -/
noncomputable def adjacentBlockCoordinates (i : Fin 4) :
    BlockSpace (adjacentLabel i) (largeBlock i) ≃ₗ[ZMod 2] Space 3 := by
  classical
  exact LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
    ((Fintype.equivFin (Block (adjacentLabel i) (largeBlock i))).trans
      (finCongr (largeBlock_card i))).symm

/-- Evaluation on the three-dimensional diagonal factor. -/
noncomputable def adjacentProjection (i : Fin 4) :
    (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (adjacentLabel i) k)) →*
      BinaryLinear.GL (BlockSpace (adjacentLabel i) (largeBlock i)) :=
  Pi.evalMonoidHom _ (largeBlock i)

/-- All omitted diagonal factors are trivial over the binary field. -/
theorem adjacentProjection_bijective (i : Fin 4) :
    Function.Bijective (adjacentProjection i) := by
  constructor
  · intro a b he
    funext k
    by_cases hk : k = largeBlock i
    · subst k
      exact he
    exact (linearBlock_eq_one_of_card_le_one _ _ (adjacent_otherBlock_card i k hk) (a k)).trans
      (linearBlock_eq_one_of_card_le_one _ _ (adjacent_otherBlock_card i k hk) (b k)).symm
  · intro a
    exact ⟨Function.update 1 (largeBlock i) a, by simp [adjacentProjection]⟩

/-- Identify the full diagonal group with its actual SL₃(2) factor. -/
noncomputable def adjacentFactorsEquiv (i : Fin 4) :
    (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (adjacentLabel i) k)) ≃* SL(3, ZMod 2) :=
  (MulEquiv.ofBijective (adjacentProjection i) (adjacentProjection_bijective i)).trans
    ((linearGroupCongr (adjacentBlockCoordinates i)).trans (slEquivLinear 3).symm)

/-- The original flag quotient followed by projection to the three-space. -/
noncomputable def adjacentQuotientEquiv (b : FiveBasis) (i : Fin 4) :
    (flagStabilizer b ({i, adjacentNode i} : Set (Fin 4))ᶜ ⧸
      pCore 2 (flagStabilizer b ({i, adjacentNode i} : Set (Fin 4))ᶜ)) ≃* SL(3, ZMod 2) :=
  (flagDiagonalQuotientEquiv b _).trans (adjacentFactorsEquiv i)

/-- The equivalence is the diagonal action on the marked three-space. -/
theorem adjacentQuotientEquiv_mk (b : FiveBasis) (i : Fin 4)
    (g : flagStabilizer b ({i, adjacentNode i} : Set (Fin 4))ᶜ) :
    adjacentQuotientEquiv b i (QuotientGroup.mk' _ g) =
      (slEquivLinear 3).symm (linearGroupCongr (adjacentBlockCoordinates i)
        (flagDiagonalAction b _ g (largeBlock i))) := rfl
end BinaryLinear.SmallParabolicLevi.TwoNodes

end
