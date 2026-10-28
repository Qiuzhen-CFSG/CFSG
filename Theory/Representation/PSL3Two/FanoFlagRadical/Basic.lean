module

public import Theory.Representation.PSL3Two.FanoCoreStructure
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition

/-!
# The transported core radicals inside the binary flag module

The point-core radical is W* and the line-core radical is W. Their evaluation
maps, followed by the inverse flag decomposition, embed W × W* in the actual
flag representation. The range is characterized by membership in the two
literal core radicals and zero in the trivial and Steinberg coordinates.
It has dimension six. We also name the literal intersection of all maximal
flag submodules; its equality with this transported sum is a separate assertion.

Source: the concrete summands in Aschbacher–Smith H.6.2(2), printed p.387,
combined manuscript of 1 March 2004.
-/

@[expose] public section

open Representation BinaryLinearThree FanoDecomposition FanoCoreStructure
noncomputable section

namespace BinaryLinearThree.FanoFlagRadical

/-- The sum of the natural line-core radical and dual-natural point-core radical. -/
def coreInjection : (W.prod W.dual).IntertwiningMap targetRepresentation :=
  (0 : (W.prod W.dual).IntertwiningMap (trivial (ZMod 2) Group (ZMod 2))).prod
    ((pointEvaluation.comp (IntertwiningMap.snd (ZMod 2) W W.dual)).prod
      ((lineEvaluation.comp (IntertwiningMap.fst (ZMod 2) W W.dual)).prod 0))

/-- The inclusion has zero trivial and Steinberg coordinates. -/
theorem coreInjection_apply (v : Vector × Module.Dual (ZMod 2) Vector) :
    coreInjection v = (0, (pointEvaluation v.2, (lineEvaluation v.1, 0))) := rfl

/-- The two core evaluation maps give an actual embedding. -/
theorem coreInjection_injective : Function.Injective coreInjection := by
  intro v w h
  apply Prod.ext
  · apply lineEvaluation_injective
    exact congrArg (fun x : Target => x.2.2.1) h
  · apply pointEvaluation_injective
    exact congrArg (fun x : Target => x.2.1) h

/-- Transport the two core radicals into the actual flag module. -/
def flagRadicalInclusion : (W.prod W.dual).IntertwiningMap flagRepresentation :=
  flagDecomposition.symm.toIntertwiningMap.comp coreInjection

/-- The transported direct sum of the two core radicals. -/
def transportedCoreRadicals : Subrepresentation flagRepresentation := flagRadicalInclusion.range

/-- The literal intersection of all maximal invariant subspaces of the flag module. -/
def flagRadical : Subrepresentation flagRepresentation :=
  sInf {N : Subrepresentation flagRepresentation | IsCoatom N}

/-- Transport preserves injectivity of the radical inclusion. -/
theorem flagRadicalInclusion_injective : Function.Injective flagRadicalInclusion :=
  flagDecomposition.symm.toLinearEquiv.injective.comp coreInjection_injective

/-- An actual representation equivalence from natural plus dual-natural to the transported sum. -/
def transportedCoreRadicalsEquiv : (W.prod W.dual).Equiv
    transportedCoreRadicals.toRepresentation := by
  let f : (W.prod W.dual).IntertwiningMap transportedCoreRadicals.toRepresentation :=
    { toLinearMap := flagRadicalInclusion.toLinearMap.rangeRestrict
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact LinearMap.congr_fun (flagRadicalInclusion.isIntertwining' g) v }
  apply f.ofBijective
  constructor
  · intro v w h
    exact flagRadicalInclusion_injective (congrArg Subtype.val h)
  · intro v
    obtain ⟨w, hw⟩ := v.property
    exact ⟨w, Subtype.ext hw⟩

/-- The transported sum has dimension six. -/
theorem finrank_transportedCoreRadicals :
    Module.finrank (ZMod 2) transportedCoreRadicals.toSubmodule = 6 := by
  rw [← transportedCoreRadicalsEquiv.toLinearEquiv.finrank_eq]
  simp [Module.finrank_prod, Subspace.dual_finrank_eq, BinaryLinearThree.Vector,
    Matrix.PSL3Two.Fano.Vector]

/-- The transported sum consists exactly of the two core radicals in flag-decomposition coordinates. -/
theorem mem_transportedCoreRadicals_iff (v : BinaryPermutation.Full Flag) :
    v ∈ transportedCoreRadicals ↔
      (flagDecomposition v).1 = 0 ∧
      (flagDecomposition v).2.1 ∈ pointKernel ∧
      (flagDecomposition v).2.2.1 ∈ lineKernel ∧
      (flagDecomposition v).2.2.2 = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    have he : flagDecomposition (flagRadicalInclusion w) = coreInjection w :=
      flagDecomposition.apply_symm_apply _
    simp only [IntertwiningMap.toLinearMap_apply, he, coreInjection_apply]
    refine ⟨trivial, ?_, ?_, trivial⟩
    · change pointEvaluation w.2 ∈ LinearMap.ker pointWeightedSum.toLinearMap
      rw [← point_exact]
      exact ⟨w.2, rfl⟩
    · change lineEvaluation w.1 ∈ LinearMap.ker lineWeightedSum.toLinearMap
      rw [← line_exact]
      exact ⟨w.1, rfl⟩
  · rintro ⟨h0, hp, hl, hs⟩
    obtain ⟨φ, hφ⟩ := (show (flagDecomposition v).2.1 ∈
        LinearMap.range pointEvaluation.toLinearMap from by rw [point_exact]; exact hp)
    obtain ⟨w, hw⟩ := (show (flagDecomposition v).2.2.1 ∈
        LinearMap.range lineEvaluation.toLinearMap from by rw [line_exact]; exact hl)
    refine ⟨(w, φ), ?_⟩
    apply flagDecomposition.toLinearEquiv.injective
    change flagDecomposition (flagDecomposition.symm (coreInjection (w, φ))) = _
    rw [flagDecomposition.apply_symm_apply, coreInjection_apply]
    exact Prod.ext h0.symm (Prod.ext hφ (Prod.ext hw hs.symm))

end BinaryLinearThree.FanoFlagRadical
end
