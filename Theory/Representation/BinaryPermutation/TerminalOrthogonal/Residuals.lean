module

public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockResidual
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel
public import Theory.ElementaryAbelian.Quotient

/-!
# Residuals of the two terminal orthogonal point stabilizers

The cubic generation and rank calculation for A₄ × A₄ discharge the numerical
inputs of the paired Borel calculation. The full swapped permutation model has
no factor 3³ in its order, so every intermediate point stabilizer has exactly
three-rank two. A marked tetrahedral product also carries an explicit quotient
map onto E₉ with elementary kernel of order sixteen; this transports the
four-block extension to the original point stabilizer.

Source: Aschbacher–Smith, G.11.2(5),(12) and 12.8.13(5),(7), combined manuscript
of 1 March 2004, printed pp.364 and 855–856.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace BinaryPermutation.TerminalOrthogonal

namespace FourBlockResidual
variable {D : Type*} [Group D]

/-- The quotient map in the marked four-block coordinates. -/
def markedQuotientMap (e : D ≃* Product) : D →* E9 :=
  productQuotientMap.comp e.toMonoidHom

lemma markedQuotientMap_surjective (e : D ≃* Product) :
    Function.Surjective (markedQuotientMap e) :=
  productQuotientMap_surjective.comp e.surjective

/-- Its kernel is the actual block Klein group, transported through the marking. -/
def markedKernelEquiv (e : D ≃* Product) : (markedQuotientMap e).ker ≃* E16 where
  toFun a := ⟨productEquiv (e a), by
    rw [← quotientMap_ker]
    change productQuotientMap (productEquiv.symm (productEquiv (e a))) = 1
    rw [productEquiv.symm_apply_apply]
    exact a.property⟩
  invFun a := ⟨e.symm (productEquiv.symm a), by
    change productQuotientMap (e (e.symm (productEquiv.symm a))) = 1
    rw [e.apply_symm_apply]
    exact show a.val ∈ quotientMap.ker from quotientMap_ker.symm ▸ a.property⟩
  left_inv a := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

lemma markedQuotientMap_kernel_card (e : D ≃* Product) :
    Nat.card (markedQuotientMap e).ker = 16 :=
  (Nat.card_congr (markedKernelEquiv e).toEquiv).trans E16_card

instance markedQuotientMap_kernel_elementary (e : D ≃* Product) :
    IsElementaryAbelian 2 (markedQuotientMap e).ker :=
  IsElementaryAbelian.of_surjective (markedKernelEquiv e).symm.toMonoidHom
    (markedKernelEquiv e).symm.surjective

/-- The quotient equivalence uses this same map, rather than an unrelated E₉. -/
def markedQuotientEquiv (e : D ≃* Product) :
    D ⧸ (markedQuotientMap e).ker ≃* E9 :=
  QuotientGroup.quotientKerEquivOfSurjective _ (markedQuotientMap_surjective e)

@[simp] lemma markedQuotientEquiv_mk (e : D ≃* Product) (d : D) :
    markedQuotientEquiv e (QuotientGroup.mk' (markedQuotientMap e).ker d) =
      markedQuotientMap e d := rfl

end FourBlockResidual

namespace PairedBorel

/-- All possible marked overgroups have the same embedded two-residual. -/
lemma stabilizer_residual (H : Subgroup Model) (hH : pairedInclusion.range ≤ H) :
    (pResidual 2 (stabilizerIn H)).map (stabilizerMap H) = embeddedBorel :=
  residual_map_stabilizer H hH FourBlockResidual.product_pResidual

/-- The concrete Borel identification with no numerical group premises. -/
def stabilizerResidualEquiv (H : Subgroup Model) (hH : pairedInclusion.range ≤ H) :
    pResidual 2 (stabilizerIn H) ≃* A4 × A4 :=
  residualEquiv H hH FourBlockResidual.product_pResidual

lemma stabilizer_residual_threeRank (H : Subgroup Model)
    (hH : pairedInclusion.range ≤ H) :
    primeRank 3 (pResidual 2 (stabilizerIn H)) = 2 :=
  residual_threeRank H hH FourBlockResidual.product_pResidual FourBlockResidual.product_primeRank

/-- The upper bound applies to the whole faithful model, including its swaps. -/
lemma model_threeRank_le : primeRank 3 Model ≤ 2 := by
  apply primeRank_le_two_of_cube_not_dvd
  rw [SemidirectProduct.card, Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

lemma stabilizer_threeRank (H : Subgroup Model) (hH : pairedInclusion.range ≤ H) :
    primeRank 3 (stabilizerIn H) = 2 := by
  apply le_antisymm
  · exact (Theory.GroupTheory.primeRank_le_of_injective 3 (stabilizerMap H)
      (H.subtype_injective.comp (stabilizerIn H).subtype_injective)).trans model_threeRank_le
  · exact stabilizer_threeRank_ge H hH FourBlockResidual.product_primeRank

end PairedBorel
end BinaryPermutation.TerminalOrthogonal
