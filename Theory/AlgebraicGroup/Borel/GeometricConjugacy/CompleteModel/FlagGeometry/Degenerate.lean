module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.Products

/-!
# Flags in dimensions zero and one

There is exactly one full flag when the vector space has dimension at most one.
Its geometric realization is the complete point scheme with its regular trivial
action. This supplies the empty-product case of the flag geometry in Borel,
*Linear Algebraic Groups*, §11.1, without projectivizing the zero vector space.
-/

@[expose] public noncomputable section

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

open Variety.Geometric

universe u
variable {k : Type u} [Field k] {V : Type u}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

def lowDimensionalFlag (hV : Module.finrank k V ≤ 1) : FullFlag k V where
  subspace
    | 0 => ⊥
    | _ + 1 => ⊤
  monotone := by
    intro i j hij
    cases i with
    | zero => exact bot_le
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact le_rfl
  finrank_eq i := by
    cases i with
    | zero => exact (finrank_bot k V).trans (Nat.zero_min _).symm
    | succ i =>
      change Module.finrank k (⊤ : Submodule k V) = min (i + 1) (Module.finrank k V)
      rw [finrank_top, min_eq_right (by omega)]

theorem eq_lowDimensionalFlag (hV : Module.finrank k V ≤ 1) (F : FullFlag k V) :
    F = lowDimensionalFlag hV := by
  apply FullFlag.ext
  intro i
  cases i with
  | zero =>
    change F.subspace 0 = ⊥
    apply Submodule.finrank_eq_zero.mp
    simpa using F.finrank_eq 0
  | succ i =>
    change F.subspace (i + 1) = ⊤
    apply Submodule.eq_top_of_finrank_eq
    exact (F.finrank_eq (i + 1)).trans (min_eq_right (by omega))

variable [IsAlgClosed k] {G : Variety k} [AlgebraicGroup G]

/-- Actual complete geometry in the two cases with no proper nonzero flag terms. -/
def flagModelOfFinrankLEOne (ρ : RationalRepresentation G V)
    (hV : Module.finrank k V ≤ 1) : FlagModel ρ where
  variety := point
  action := pointAction
  pointEquiv := {
    toFun := fun _ => lowDimensionalFlag hV
    invFun := fun _ => default
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun F => (eq_lowDimensionalFlag hV F).symm }
  equivariant _ _ := (eq_lowDimensionalFlag hV _).symm
  complete := point_isComplete

theorem nonempty_flagModel_of_finrank_le_one (ρ : RationalRepresentation G V)
    (hV : Module.finrank k V ≤ 1) : Nonempty (FlagModel ρ) :=
  ⟨flagModelOfFinrankLEOne ρ hV⟩

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry
