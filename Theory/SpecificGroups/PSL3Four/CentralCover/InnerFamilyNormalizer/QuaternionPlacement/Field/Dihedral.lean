module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Field.Model

/-!
# A dihedral sixteen in the binary graph model

Write `J` for the antidiagonal binary permutation matrix and `u = 1 + E₁₂`.
The elements `(uJ, graph)` and `(J, graph)` generate a dihedral group of
order sixteen in `SL₃(2) ⋊ C₂`: their product is a transvection and the square
of the rotation is the regular upper-unitriangular matrix of order four.
The explicit sixteen normal forms give a multiplicative injection, verified
by kernel reduction. Taking the product with the field factor gives a group
of order thirty-two in the model.

`candidateHom` maps that group to the actual Frobenius centralizer. Its
injectivity after this map is a separate obligation; the abstract model
injection does not imply faithfulness of the projective action.

This supplies the candidate for the field-involution centralizer calculation
used in Aschbacher–Smith, printed p.1192, with 16.1.4(4), printed p.1171,
`refs/quasithin.pdf`.
-/

@[expose] public section
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Field
noncomputable section

def rotationMatrix : Binary := ⟨!![0, 1, 1; 0, 1, 0; 1, 0, 0], by decide⟩
def reflectionMatrix : Binary := ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩
def rotation : GraphModel := ⟨rotationMatrix, Multiplicative.ofAdd 1⟩
def reflection : GraphModel := ⟨reflectionMatrix, Multiplicative.ofAdd 1⟩

def dihedralMap : DihedralGroup 8 → GraphModel
  | .r i => rotation ^ i.val
  | .sr i => reflection * rotation ^ i.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def dihedralHom : DihedralGroup 8 →* GraphModel where
  toFun := dihedralMap
  map_one' := by decide +kernel
  map_mul' := by
    intro x y
    apply SemidirectProduct.ext <;> revert x y <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem dihedralHom_injective : Function.Injective dihedralHom := by
  have h : Function.Injective (fun x => ((dihedralMap x).left, (dihedralMap x).right)) := by
    decide +kernel
  intro x y hxy
  exact h (congrArg (fun z : GraphModel => (z.left, z.right)) hxy)

def candidateModelHom : DihedralGroup 8 × C2 →* Model :=
  dihedralHom.prodMap (MonoidHom.id C2)

/-- The explicit order-thirty-two candidate mapped into the actual centralizer. -/
def candidateHom : DihedralGroup 8 × C2 →* C := modelHom.comp candidateModelHom

theorem candidateModelHom_injective : Function.Injective candidateModelHom := by
  intro x y h
  apply Prod.ext
  · exact dihedralHom_injective (congrArg Prod.fst h)
  · exact congrArg (fun z : Model => z.2) h

end
end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Field
