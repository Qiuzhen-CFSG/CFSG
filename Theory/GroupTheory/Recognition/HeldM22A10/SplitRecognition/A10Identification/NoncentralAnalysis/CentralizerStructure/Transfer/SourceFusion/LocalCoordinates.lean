module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.Model

/-!
# Representatives for the centralizer quotient

These 32 words in the concrete local group centralize mu and are distinct
modulo its order-two subgroup. Their multiplication agrees modulo mu with
C2 × C2 × D8. Kernel reduction checks the finite words; ambient fusion is
not a consequence of these calculations.

Source: Held, Illinois J. Math. 13 (1969), 224–240, p.233,
DOI 10.1215/ijm/1256053756.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion
open TransferModel (Model)
namespace Local
open Coordinates

@[expose] public def dihedralWord : DihedralGroup 4 → H
  | .r i => (tau * Coordinates.mup) ^ i.val
  | .sr i => tau * (tau * Coordinates.mup) ^ i.val

@[expose] public def liftWord (x : Model) : H :=
  lam ^ x.1.toAdd.val * xi ^ x.2.1.toAdd.val * dihedralWord x.2.2

set_option maxHeartbeats 2000000 in
public theorem liftWord_commutes : ∀ x : Model, liftWord x * Coordinates.mu = Coordinates.mu * liftWord x := by decide +kernel

set_option maxHeartbeats 8000000 in
public theorem liftWord_mul : ∀ x y : Model,
    liftWord x * liftWord y = liftWord (x*y) ∨
    liftWord x * liftWord y = Coordinates.mu * liftWord (x*y) := by decide +kernel

set_option maxHeartbeats 8000000 in
public theorem liftWord_injective_mod_mu : ∀ x y : Model,
    (liftWord x = liftWord y ∨ liftWord x = Coordinates.mu * liftWord y) → x = y := by decide +kernel

public theorem liftWord_p : liftWord TransferModel.p = Coordinates.pi := by decide +kernel
public theorem liftWord_l : liftWord TransferModel.l = lam := by decide +kernel
public theorem liftWord_z : liftWord TransferModel.z = xi := by decide +kernel
public theorem liftWord_t : liftWord TransferModel.t = tau := by decide +kernel
public theorem liftWord_m : liftWord TransferModel.m = mup := by decide +kernel
end Local

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion
