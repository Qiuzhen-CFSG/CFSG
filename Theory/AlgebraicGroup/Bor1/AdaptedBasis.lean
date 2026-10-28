module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

universe u v

namespace Theory.AlgebraicGroup.Bor1

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A subspace's fixed finite basis extends, in the same order, to an ambient
finite basis. -/
public theorem exists_basis_extends_finBasis (W : Submodule k V) :
    ∃ (e : Module.Basis (Fin (Module.finrank k V)) k V)
      (hr : Module.finrank k W ≤ Module.finrank k V),
      ∀ j : Fin (Module.finrank k W),
        e (Fin.castLE hr j) = (Module.finBasis k W j : V) := by
  let bW := Module.finBasis k W
  let bQ := Module.finBasis k (V ⧸ W)
  have hdim : Module.finrank k W + Module.finrank k (V ⧸ W) =
      Module.finrank k V := by
    rw [add_comm]
    exact W.finrank_quotient_add_finrank
  let idx : (Fin (Module.finrank k W) ⊕ Fin (Module.finrank k (V ⧸ W))) ≃
      Fin (Module.finrank k V) := finSumFinEquiv.trans (finCongr hdim)
  let e := (bW.sumQuot bQ).reindex idx
  have hr : Module.finrank k W ≤ Module.finrank k V := by omega
  refine ⟨e, hr, ?_⟩
  intro j
  have hj : idx (Sum.inl j) = Fin.castLE hr j := by
    apply Fin.ext
    rfl
  rw [← hj]
  simp [e, idx, bW, Module.Basis.reindex_apply]

end Theory.AlgebraicGroup.Bor1
