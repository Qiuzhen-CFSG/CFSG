module

public import Theory.GroupTheory.Recognition.HeldM22A10.Setup
public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.ComplementAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.Actions
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# Binary coordinates for the split Held centralizer

The elementary kernel of order sixteen has dimension four over F2. A basis
and the quotient identification K ≃ S4 transport the actual conjugation action
to the fixed binary four-space. The semidirect-product congruence identifies
its product with the original centralizer. Faithfulness, the centralizer's
center order and every Sylow center order are transported with this equivalence.
No ambient simplicity is needed for these reductions.

This supplies coordinates for the remark on p.224 of D. Held, "A
Characterization of some multiply transitive permutation groups, I", Illinois
J. Math. 13 (1969), 224–240, DOI 10.1215/ijm/1256053756. It does not classify
the resulting action. In particular the full source hypotheses, including
ambient simplicity, remain available to that classification step.
-/

open scoped IsMulCommutative

namespace Theory.GroupTheory.HeldM22A10
namespace LocalData
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)

/-- Binary coordinates on the actual elementary kernel, obtained from a basis. -/
@[expose] public noncomputable def kernelBinaryEquiv : D.kernel ≃* LocalModelDichotomy.BinaryFour := by
  classical
  let := D.kernel_elementary
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive D.kernel) = 2 ^ 4 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.kernel)
    change Nat.card D.kernel = _ at hsize
    simpa only [Nat.card_zmod, D.kernel_card, show (2 : ℕ) ^ 4 = 16 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive D.kernel) = 4 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive D.kernel) hdim
  exact b.equivFun.toAddEquiv.toMultiplicativeRight

/-- The actual complement conjugation action, in binary and S4 coordinates. -/
@[expose] public noncomputable def binaryAction (K : Subgroup D.centralizer)
    (hK : D.kernel.IsComplement' K) :
    LocalModelDichotomy.SymmetricFour →* MulAut LocalModelDichotomy.BinaryFour :=
  (MulAut.congr D.kernelBinaryEquiv).toMonoidHom.comp
    ((D.complementAction K).comp (D.complementEquiv K hK).symm.toMonoidHom)

/-- The binary action agrees with conjugation by the supplied complement. -/
public theorem binaryAction_apply_kernel (K : Subgroup D.centralizer)
    (hK : D.kernel.IsComplement' K) (s : LocalModelDichotomy.SymmetricFour) (f : D.kernel) :
    D.binaryAction K hK s (D.kernelBinaryEquiv f) =
      D.kernelBinaryEquiv (D.complementAction K ((D.complementEquiv K hK).symm s) f) := by
  change D.kernelBinaryEquiv (D.complementAction K ((D.complementEquiv K hK).symm s)
    (D.kernelBinaryEquiv.symm (D.kernelBinaryEquiv f))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Binary coordinates identify the original centralizer with this exact action. -/
@[expose] public noncomputable def binarySemidirectEquiv (K : Subgroup D.centralizer)
    (hK : D.kernel.IsComplement' K) :
    LocalModelDichotomy.BinaryFour ⋊[D.binaryAction K hK] LocalModelDichotomy.SymmetricFour ≃*
      D.centralizer :=
  (SemidirectProduct.congr' D.kernelBinaryEquiv (D.complementEquiv K hK)).symm.trans
    (D.complementSemidirectEquiv K hK)

/-- Changing coordinates preserves faithfulness of complement conjugation. -/
public theorem binaryAction_injective (K : Subgroup D.centralizer)
    (hK : D.kernel.IsComplement' K) : Function.Injective (D.binaryAction K hK) :=
  (MulAut.congr D.kernelBinaryEquiv).injective.comp
    ((D.complementAction_injective K hK).comp (D.complementEquiv K hK).symm.injective)

/-- The normalized semidirect product has center of order two. -/
public theorem binarySemidirect_center_card (K : Subgroup D.centralizer)
    (hK : D.kernel.IsComplement' K) :
    Nat.card (Subgroup.center
      (LocalModelDichotomy.BinaryFour ⋊[D.binaryAction K hK] LocalModelDichotomy.SymmetricFour)) = 2 :=
  (Nat.card_congr (Subgroup.centerCongr (D.binarySemidirectEquiv K hK)).toEquiv).trans
    D.center_card

/-- Every Sylow two-subgroup of the normalized product has center of order two. -/
public theorem binarySemidirect_sylow_center_card (K : Subgroup D.centralizer)
    (hK : D.kernel.IsComplement' K)
    (P : Sylow 2 (LocalModelDichotomy.BinaryFour ⋊[D.binaryAction K hK]
      LocalModelDichotomy.SymmetricFour)) : Nat.card (Subgroup.center P) = 2 := by
  let e := D.binarySemidirectEquiv K hK
  let : Finite (LocalModelDichotomy.BinaryFour ⋊[D.binaryAction K hK]
      LocalModelDichotomy.SymmetricFour) := Finite.of_equiv D.centralizer e.symm.toEquiv
  let Q : Sylow 2 (LocalModelDichotomy.BinaryFour ⋊[D.binaryAction K hK]
      LocalModelDichotomy.SymmetricFour) :=
    D.localSylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let f : D.localSylow ≃* Q := e.symm.subgroupMap D.localSylow
  let g : D.localSylow ≃* D.sylow :=
    Subgroup.subgroupOfEquivOfLe D.sylow_le_centralizer
  let h : P ≃* D.sylow := ((P.equiv Q).trans f.symm).trans g
  exact (Nat.card_congr (Subgroup.centerCongr h).toEquiv).trans (D.sylow_center_card K hK)

end LocalData
end Theory.GroupTheory.HeldM22A10
