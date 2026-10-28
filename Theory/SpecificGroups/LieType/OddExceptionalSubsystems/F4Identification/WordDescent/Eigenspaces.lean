module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.E6Folding

/-!
# The two diagram eigenspace actions of the folded E6 subgroup

The literal pinned E6 involution permutes Cartan and root coordinates. Every
folded generator, and hence every folded matrix, commutes with this permutation.
Its eigenspaces are therefore invariant and carry genuine linear actions of the
existing folded subgroup. The projections `(v + diagram v) / 2` and
`(v - diagram v) / 2` show that these two actions jointly detect a matrix when
2 is invertible. In particular this decomposition is valid in characteristic 3;
no simplicity or irreducibility assertion is used.

These are actions of the folded subgroup. Descent of the complementary action
from the F4 matrix cover is separate mathematics, not a premise hidden in the
definitions. The fixed action is the target of the independent F4 adjoint-block
comparison. The word-level consumer is `F4Identification.WordDescent`.

Source: the F4 folding in GLS3 §§2.3, 2.6 and the inclusions used in
Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open scoped Matrix
open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.F4Identification.WordDescent
variable (F : Type*) [Field F]
attribute [local instance] Classical.decEq

/-- The literal E6 Cartan-plus-root coordinate space. -/
abbrev Space := Index → F

/-- The existing pinned index involution acting on column vectors. -/
def diagramLinear : Space F →ₗ[F] Space F where
  toFun v i := v (typeE6PinnedIndexEquiv i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem diagramLinear_twice (v : Space F) :
    diagramLinear F (diagramLinear F v) = v := by
  ext i
  exact congrArg v (typeE6PinnedIndexEquiv_twice i)

/-- An eigenspace of the pinned coordinate involution. -/
def eigenspace (a : F) : Submodule F (Space F) where
  carrier := {v | diagramLinear F v = a • v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change diagramLinear F (v + w) = a • (v + w)
    rw [map_add, hv, hw, smul_add]
  smul_mem' := by
    intro c v hv
    change diagramLinear F (c • v) = a • (c • v)
    rw [map_smul, hv, smul_comm]

@[simp] theorem mem_eigenspace (a : F) (v : Space F) :
    v ∈ eigenspace F a ↔ diagramLinear F v = a • v := Iff.rfl

abbrev fixedSpace := eigenspace F 1
abbrev complementSpace := eigenspace F (-1)

/-- The underlying matrix, without changing its basis or pinning. -/
def foldedMatrix (g : splitSubgroup F) : Matrix Index Index F := g.val.val.val

@[simp] theorem foldedMatrix_one : foldedMatrix F 1 = 1 := rfl
@[simp] theorem foldedMatrix_mul (g h : splitSubgroup F) :
    foldedMatrix F (g * h) = foldedMatrix F g * foldedMatrix F h := rfl

theorem foldedMatrix_diagram (g : splitSubgroup F) (i j : Index) :
    foldedMatrix F g (typeE6PinnedIndexEquiv i) (typeE6PinnedIndexEquiv j) =
      foldedMatrix F g i j := by
  have h := congrArg (fun x : splitCarrier F => x.val.val i j)
    (splitSubgroup_fixed F g.property)
  simpa only [pinnedDiagram_entry, foldedMatrix] using h

theorem diagramLinear_mulVec (g : splitSubgroup F) (v : Space F) :
    diagramLinear F (foldedMatrix F g *ᵥ v) =
      foldedMatrix F g *ᵥ diagramLinear F v := by
  ext i
  change (∑ j, foldedMatrix F g (typeE6PinnedIndexEquiv i) j * v j) =
    ∑ j, foldedMatrix F g i j * v (typeE6PinnedIndexEquiv j)
  rw [← Equiv.sum_comp typeE6PinnedIndexEquiv
    (fun j => foldedMatrix F g (typeE6PinnedIndexEquiv i) j * v j)]
  simp only [foldedMatrix_diagram]

theorem mulVec_mem_eigenspace (a : F) (g : splitSubgroup F)
    (v : eigenspace F a) : foldedMatrix F g *ᵥ (v : Space F) ∈ eigenspace F a := by
  rw [mem_eigenspace, diagramLinear_mulVec, v.property, Matrix.mulVec_smul]

/-- Restriction of the actual folded matrix action to a diagram eigenspace. -/
def eigenspaceAction (a : F) :
    splitSubgroup F →* (eigenspace F a ≃ₗ[F] eigenspace F a) where
  toFun g :=
    { toFun := fun v => ⟨foldedMatrix F g *ᵥ (v : Space F),
        mulVec_mem_eigenspace F a g v⟩
      invFun := fun v => ⟨foldedMatrix F g⁻¹ *ᵥ (v : Space F),
        mulVec_mem_eigenspace F a g⁻¹ v⟩
      left_inv := by
        intro v
        apply Subtype.ext
        change foldedMatrix F g⁻¹ *ᵥ (foldedMatrix F g *ᵥ (v : Space F)) = v
        rw [Matrix.mulVec_mulVec, ← foldedMatrix_mul, inv_mul_cancel,
          foldedMatrix_one, Matrix.one_mulVec]
      right_inv := by
        intro v
        apply Subtype.ext
        change foldedMatrix F g *ᵥ (foldedMatrix F g⁻¹ *ᵥ (v : Space F)) = v
        rw [Matrix.mulVec_mulVec, ← foldedMatrix_mul, mul_inv_cancel,
          foldedMatrix_one, Matrix.one_mulVec]
      map_add' := by
        intro v w
        apply Subtype.ext
        exact Matrix.mulVec_add _ _ _
      map_smul' := by
        intro c v
        apply Subtype.ext
        exact Matrix.mulVec_smul _ _ _ }
  map_one' := by
    ext v i
    exact congrFun (Matrix.one_mulVec (v : Space F)) i
  map_mul' g h := by
    ext v i
    exact congrFun (Matrix.mulVec_mulVec (v : Space F) (foldedMatrix F g)
      (foldedMatrix F h)).symm i

@[simp] theorem eigenspaceAction_apply (a : F) (g : splitSubgroup F)
    (v : eigenspace F a) :
    (eigenspaceAction F a g v : Space F) = foldedMatrix F g *ᵥ (v : Space F) := rfl

def fixedPart (v : Space F) : fixedSpace F :=
  ⟨(2 : F)⁻¹ • (v + diagramLinear F v), by
    simp [mem_eigenspace, map_smul, map_add, add_comm]⟩

def complementPart (v : Space F) : complementSpace F :=
  ⟨(2 : F)⁻¹ • (v - diagramLinear F v), by
    simp only [mem_eigenspace, map_smul, map_sub, diagramLinear_twice]
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring⟩

theorem fixedPart_add_complementPart (htwo : (2 : F) ≠ 0) (v : Space F) :
    (fixedPart F v : Space F) + complementPart F v = v := by
  ext i
  change (2 : F)⁻¹ * (v i + diagramLinear F v i) +
    (2 : F)⁻¹ * (v i - diagramLinear F v i) = v i
  field_simp
  ring

/-- Both diagram blocks together detect the identity, also in characteristic three. -/
theorem eq_one_of_eigenspaceActions (htwo : (2 : F) ≠ 0) (g : splitSubgroup F)
    (hp : eigenspaceAction F 1 g = 1)
    (hn : eigenspaceAction F (-1) g = 1) : g = 1 := by
  have hv (v : Space F) : foldedMatrix F g *ᵥ v = v := by
    have hpv := congrArg (fun e : fixedSpace F ≃ₗ[F] fixedSpace F =>
      (e (fixedPart F v) : Space F)) hp
    have hnv := congrArg (fun e : complementSpace F ≃ₗ[F] complementSpace F =>
      (e (complementPart F v) : Space F)) hn
    change foldedMatrix F g *ᵥ (fixedPart F v : Space F) = fixedPart F v at hpv
    change foldedMatrix F g *ᵥ (complementPart F v : Space F) =
      complementPart F v at hnv
    rw [← fixedPart_add_complementPart F htwo v, Matrix.mulVec_add, hpv, hnv]
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  change foldedMatrix F g i j = (1 : Matrix Index Index F) i j
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply,
    Matrix.one_apply, eq_comm] using congrFun (hv (Pi.single j 1)) i

end TwistedE6.FoldedSubsystem.F4Identification.WordDescent
