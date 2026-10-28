module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.Series
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.SimpleSupport.TraceSeries

/-!
# Trace additivity along an exhaustive vertex series

Identify the smaller invariant space inside its successor, apply trace
additivity to the literal quotient, and telescope from zero to the whole
representation. This supplies the trace identity for the vertex families in
Feit VII.2.20 and VII.2.25, using their actual quotient actions.
-/

public section
noncomputable section
open scoped BigOperators

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K G V}

private def insideEquiv (U W : Subrepresentation ρ) (h : U ≤ W) :
    U.toRepresentation.Equiv (inside U W).toRepresentation where
  toFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl

private def topEquiv : (⊤ : Subrepresentation ρ).toRepresentation.Equiv ρ where
  toFun x := x.val
  invFun x := ⟨x, Submodule.mem_top⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl

/-- The trace character of an exhaustive series is the sum of its actual factors. -/
theorem ExhaustiveSeries.character_sum {s : ℕ} (c : ExhaustiveSeries ρ s) :
    ρ.character = ∑ i, (c.factor i).character := by
  have hterm (i : Fin s) : (c.term i.succ).toRepresentation.character =
      (c.term i.castSucc).toRepresentation.character + (c.factor i).character := by
    have h := character_eq_subrepresentation_add_quotient (c.term i.succ).toRepresentation
      (inside (c.term i.castSucc) (c.term i.succ))
    have he := char_iso (insideEquiv (c.term i.castSucc) (c.term i.succ)
      (c.term.monotone (by exact Fin.le_iff_val_le_val.mpr (Nat.le_succ _))))
    exact h.trans (congrArg (· + (c.factor i).character) he.symm)
  have hf : (c.term 0).toRepresentation.character = 0 := by
    rw [c.first]
    have : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule := by
      change Subsingleton (⊥ : Submodule K V)
      infer_instance
    funext g
    change LinearMap.trace K (⊥ : Subrepresentation ρ).toSubmodule _ = 0
    exact (congrArg (LinearMap.trace K (⊥ : Subrepresentation ρ).toSubmodule)
      (Subsingleton.elim ((⊥ : Subrepresentation ρ).toRepresentation g) 0)).trans (map_zero _)
  have hl : (c.term (Fin.last s)).toRepresentation.character = ρ.character := by
    rw [c.last]
    exact char_iso topEquiv
  have hs := (Fin.sum_univ_succ (fun i => (c.term i).toRepresentation.character)).symm.trans
    (Fin.sum_univ_castSucc (fun i => (c.term i).toRepresentation.character))
  rw [hf, zero_add, hl] at hs
  have he (i : Fin s) : (c.factor i).character =
      (c.term i.succ).toRepresentation.character -
        (c.term i.castSucc).toRepresentation.character := by
    rw [hterm, add_sub_cancel_left]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, hs, add_sub_cancel_left]
end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
