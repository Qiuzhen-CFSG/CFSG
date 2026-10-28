module
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Index
/-!
# A point stabilizer in the binary natural three-space

SL₃(2) is transitive on the seven nonzero vectors. Orbit--stabilizer and
its order 168 give a point stabilizer of order 24. These are the concrete
model inputs for the original component centralizer in Aschbacher--Smith,
10.2.9, printed p.753; no abstract group-family tag is used.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace BinaryLinear.NaturalThreePoint

theorem stabilizer_index (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    (MulAction.stabilizer SL(3,ZMod 2) v).index = 7 := by
  have ho : MulAction.orbit SL(3,ZMod 2) v = ({0} : Set (Fin 3 → ZMod 2))ᶜ := by
    ext w
    constructor
    · rintro ⟨g,rfl⟩ hw
      apply hv
      have hh : g • v = 0 := hw
      simpa using congrArg (fun w : Fin 3 → ZMod 2 => g⁻¹ • w) hh
    · intro hw
      obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three v w hv hw
      exact ⟨g,hg⟩
  rw [MulAction.index_stabilizer,ho,Set.ncard_compl,Set.ncard_singleton]
  norm_num [Nat.card_fun]

theorem group_card : Nat.card SL(3,ZMod 2) = 168 := by
  rw [Nat.card_congr ((OuterCyclic.slEquivLinear 3).trans
    (OuterCyclic.matrixEquivLinear 3).symm).toEquiv,Matrix.card_GL_field]
  decide

theorem stabilizer_card (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    Nat.card (MulAction.stabilizer SL(3,ZMod 2) v) = 24 := by
  have h := (MulAction.stabilizer SL(3,ZMod 2) v).index_mul_card
  rw [stabilizer_index v hv,group_card] at h
  omega

end BinaryLinear.NaturalThreePoint
