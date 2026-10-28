module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Intertwiners

/-!
# The cyclic kernel criterion

A rank-one kernel bound and cyclic vectors in the module and its dual
give irreducibility. The finite restriction of an injective map is surjective.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
open Matrix

theorem irreducible_of_cyclic_kernel (X Y : BinaryMatrix) (r l e : BinaryVector)
    (hreconstruct : Y * X + vecMulVec r e = 1)
    (hleft : vecMul l X = 0)
    (hstable : ∀ W : Submodule (ZMod 2) BinaryVector,
      (∀ v ∈ W, matrixA.mulVec v ∈ W) →
      (∀ v ∈ W, matrixB.mulVec v ∈ W) → ∀ v ∈ W, X.mulVec v ∈ W)
    (hcolumn : ∀ W : Submodule (ZMod 2) BinaryVector,
      (∀ v ∈ W, matrixA.mulVec v ∈ W) →
      (∀ v ∈ W, matrixB.mulVec v ∈ W) → r ∈ W → W = ⊤)
    (hrow : ∀ W : Submodule (ZMod 2) BinaryVector,
      (∀ v ∈ W, vecMul v matrixA ∈ W) →
      (∀ v ∈ W, vecMul v matrixB ∈ W) → l ∈ W → W = ⊤) :
    GeneratorIrreducible := by
  intro W hA hB
  by_cases hr : r ∈ W
  · exact Or.inr (hcolumn W hA hB hr)
  left
  have hzero : ∀ v ∈ W, X.mulVec v = 0 → v = 0 := by
    intro v hv hx
    have heq := congrArg (fun M : BinaryMatrix => M.mulVec v) hreconstruct
    rw [add_mulVec, ← mulVec_mulVec, hx, mulVec_zero, zero_add,
      vecMulVec_mulVec, op_smul_eq_smul, one_mulVec] at heq
    by_cases hc : e ⬝ᵥ v = 0
    · simpa only [hc, zero_smul] using heq.symm
    · exact (hr ((W.smul_mem_iff hc).mp (heq.symm ▸ hv))).elim
  let f : W → W := fun v => ⟨X.mulVec v, hstable W hA hB v v.property⟩
  have hinj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hzero (v.val - w.val) (W.sub_mem v.property w.property)
    rw [mulVec_sub]
    have h' := congrArg Subtype.val h
    change X.mulVec v.val = X.mulVec w.val at h'
    exact sub_eq_zero.mpr h'
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  let U : Submodule (ZMod 2) BinaryVector :=
    { carrier := {z | ∀ w ∈ W, z ⬝ᵥ w = 0}
      zero_mem' := by intro w _; exact zero_dotProduct w
      add_mem' := by
        intro z z' hz hz' w hw
        rw [add_dotProduct, hz w hw, hz' w hw, zero_add]
      smul_mem' := by
        intro c z hz w hw
        rw [smul_dotProduct, hz w hw, smul_zero] }
  have hl : l ∈ U := by
    intro w hw
    obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
    have hv' := congrArg Subtype.val hv
    change X.mulVec v.val = w at hv'
    rw [← hv', dotProduct_mulVec, hleft, zero_dotProduct]
  have hU : U = ⊤ := hrow U
    (fun z hz w hw => by rw [← dotProduct_mulVec]; exact hz _ (hA w hw))
    (fun z hz w hw => by rw [← dotProduct_mulVec]; exact hz _ (hB w hw)) hl
  apply bot_unique
  intro w hw
  change w = 0
  funext i
  have hi : Pi.single i (1 : ZMod 2) ∈ U := by rw [hU]; trivial
  simpa only [single_dotProduct, one_mul, Pi.zero_apply] using hi w hw

end Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
