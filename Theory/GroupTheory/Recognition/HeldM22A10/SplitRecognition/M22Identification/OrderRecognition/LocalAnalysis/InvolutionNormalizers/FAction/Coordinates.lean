module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Model
public import Mathlib.Data.Fin.Init

/-!
# Coordinates and local orbits on the second elementary sixteen

The four generators z₁, z₃, a, d identify F with four binary bits.
Multiplication is xor. The coordinate Sylow group has orbits represented
by the bit words 0, 1, 2, 4, 8, with sizes 1, 1, 2, 4, 8.
Every orbit witness below is checked in the kernel against the actual
conjugation action. These coordinates are shared by the orbit argument
and the remaining finite automizer identification.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, pp.4–5.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance : DecidablePred (· ∈ modelF) := fun x =>
  decidable_of_iff (x * d = d * x) mem_centralizer_singleton_iff.symm
local instance : DecidablePred (· ∈ modelT) := fun x =>
  decidable_of_iff (x.right * a.right = a.right * x.right) mem_centralizer_singleton_iff.symm

public abbrev pointY : modelF := ⟨z 2, modelF_generators.2.1⟩
public abbrev pointA : modelF := ⟨a, modelF_generators.2.2.1⟩
@[expose] public def word (i : Fin 16) : modelF :=
  (if i.val.testBit 0 then pointZ else 1) *
  (if i.val.testBit 1 then pointY else 1) *
  (if i.val.testBit 2 then pointA else 1) *
  (if i.val.testBit 3 then pointD else 1)

public theorem word_zero : word 0 = 1 := by decide +kernel
public theorem word_one : word 1 = pointZ := by decide +kernel
public theorem word_eight : word 8 = pointD := by decide +kernel
public theorem word_injective : Function.Injective word := by decide +kernel
public theorem word_surjective : Function.Surjective word := by decide +kernel
public theorem word_xor : ∀ i j : Fin 16, word (i ^^^ j) = word i * word j := by decide +kernel

@[expose] public def representative (i : Fin 16) : Fin 16 :=
  if i = 0 then 0 else if i = 1 then 1 else if i < 4 then 2 else if i < 8 then 4 else 8

@[expose] public def localAction : modelT →* MulAut modelF :=
  modelF.normalizerMonoidHom.comp (inclusion (show modelT ≤ normalizer (modelF : Set TwistedModel) from
    modelF_normalizer ▸ le_rfl))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
public theorem local_orbit_witness : ∀ i : Fin 16, ∃ t : modelT,
    localAction t (word (representative i)) = word i := by decide +kernel

public theorem localAction_mem (t : modelT) : localAction t ∈ localAutomizer :=
  ⟨inclusion (modelF_normalizer ▸ le_rfl) t, rfl⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction
