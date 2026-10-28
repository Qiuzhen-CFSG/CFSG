module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Realization.Support
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Explicit paired coordinates for invariant symplectic tensor support

Cut a support invariant under addition of r modulo 2r at the first r indices.
The half-turn pairs each first-half index with exactly one second-half index.
Reindex the tensor-product coordinate basis by these two halves. The literal
product-of-matrix-entries formula identifies the resulting action with the
half tensor and its twist by graphDerived to the power r.

Source: Guralnick--Malle, Classification of 2F-modules II, Section 3.5 and
Proposition 6.2(2--3); GLS3, Examples 2.8.10(d); Aschbacher--Smith K.3.4,
printed pp.456--457.
-/

public section

open Representation Representation.FrobeniusTensor Fin.NatCast
open scoped TensorProduct
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
noncomputable section

variable {r : ℕ} [NeZero (2*r)]

/-- The factors whose indices belong to the first half of the graph cycle. -/
@[expose] def halfSupport (S : Finset (Fin (2*r))) : Finset (Fin (2*r)) :=
  S.filter (fun j => (j : ℕ) < r)

private theorem shift_twice (j : Fin (2*r)) :
    (j + (r : Fin (2*r))) + (r : Fin (2*r)) = j := by
  rw [add_assoc, ← Nat.cast_add]
  have hh : r+r = 2*r := by omega
  rw [hh]
  simp

private theorem shift_low_iff (j : Fin (2*r)) :
    (j + (r : Fin (2*r))).val < r ↔ ¬ j.val < r := by
  have hr : 0 < r := by have := NeZero.ne (2*r); omega
  have hj := j.isLt
  simp only [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : r < 2*r)]
  by_cases hl : j.val < r
  · rw [Nat.mod_eq_of_lt (by omega : j.val + r < 2*r)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : 2*r ≤ j.val+r)]
    rw [Nat.mod_eq_of_lt (by omega : j.val+r-2*r < 2*r)]
    omega

private theorem shift_mem (S : Finset (Fin (2*r))) (hS : halfTurnSupport S = S)
    (j : Fin (2*r)) : j + (r : Fin (2*r)) ∈ S ↔ j ∈ S := by
  conv_lhs => rw [← hS]
  simp [halfTurnSupport]

private def supportIndex (S : Finset (Fin (2*r))) (hS : halfTurnSupport S = S) :
    (halfSupport S ⊕ halfSupport S) ≃ S where
  toFun := Sum.elim (fun j => ⟨j.val, (Finset.mem_filter.mp j.property).1⟩)
    (fun j => ⟨j.val + (r : Fin (2*r)),
      (shift_mem S hS j.val).mpr (Finset.mem_filter.mp j.property).1⟩)
  invFun j := if hj : j.val.val < r then
      Sum.inl ⟨j.val, Finset.mem_filter.mpr ⟨j.property, hj⟩⟩
    else Sum.inr ⟨j.val + (r : Fin (2*r)), Finset.mem_filter.mpr
      ⟨(shift_mem S hS j.val).mpr j.property, (shift_low_iff j.val).mpr hj⟩⟩
  left_inv j := by
    cases j with
    | inl j => simp [(Finset.mem_filter.mp j.property).2]
    | inr j =>
      have hj := (Finset.mem_filter.mp j.property).2
      simp [hj, shift_low_iff, shift_twice]
  right_inv j := by
    dsimp only
    split <;> simp [shift_twice]

private def pairedIndex (S : Finset (Fin (2*r))) (hS : halfTurnSupport S = S) :
    (S → Coordinate) ≃ ((halfSupport S → Coordinate) × (halfSupport S → Coordinate)) :=
  (Equiv.arrowCongr (supportIndex S hS).symm (Equiv.refl Coordinate)).trans
    (Equiv.sumArrowEquivProdArrow (halfSupport S) (halfSupport S) Coordinate)

variable {F E : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Field E]

private def pairedCoordinates (S : Finset (Fin (2*r))) (hS : halfTurnSupport S = S) :
    (((halfSupport S → Coordinate) → E) ⊗[E] ((halfSupport S → Coordinate) → E)) ≃ₗ[E]
      ((S → Coordinate) → E) :=
  ((Pi.basisFun E (halfSupport S → Coordinate)).tensorProduct
    (Pi.basisFun E (halfSupport S → Coordinate))).equivFun.trans
      (LinearEquiv.funCongrLeft E E (pairedIndex S hS))

private theorem pairedCoordinates_tmul (S : Finset (Fin (2*r))) (hS : halfTurnSupport S = S)
    (v w : (halfSupport S → Coordinate) → E) (x : S → Coordinate) :
    pairedCoordinates S hS (v ⊗ₜ[E] w) x =
      v ((pairedIndex S hS x).1) * w ((pairedIndex S hS x).2) := by
  simp only [pairedCoordinates, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
    Module.Basis.equivFun_apply, LinearMap.funLeft_apply]
  simpa only [Pi.basisFun_repr, smul_eq_mul, mul_comm] using
    (Module.Basis.tensorProduct_repr_tmul_apply
      (Pi.basisFun E (halfSupport S → Coordinate))
      (Pi.basisFun E (halfSupport S → Coordinate))
      v w (pairedIndex S hS x).1 (pairedIndex S hS x).2)

private theorem tensorMatrix_pair (hF : Nat.card F = 2^r) (e : F →+* E)
    (S : Finset (Fin (2*r))) (hS : halfTurnSupport S = S)
    (g : Derived F) (x y : S → Coordinate) :
    tensorMatrix e S g x y =
      tensorMatrix e (halfSupport S) g ((pairedIndex S hS x).1) ((pairedIndex S hS y).1) *
      tensorMatrix e (halfSupport S) ((graphDerived F ^ r) g)
        ((pairedIndex S hS x).2) ((pairedIndex S hS y).2) := by
  classical
  rw [tensorMatrix, ← (supportIndex S hS).prod_comp, Fintype.prod_sum_type]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hp : graphDerived F ^ ((j.val + (r : Fin (2*r)) : Fin (2*r)) : ℕ) =
      graphDerived F ^ (j.val : ℕ) * graphDerived F ^ r := by
    rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod,
      ← pow_eq_pow_mod _ (graphDerived_pow_field hF), pow_add]
  change e (((graphDerived F ^ ((j.val + (r : Fin (2*r))).val)) g).val.val _ _) = _
  rw [hp]
  rfl

/-- An actual intertwiner between the full tensor and its two graph-paired halves. -/
def tensorModel_paired_equiv (hF : Nat.card F = 2^r) (e : F →+* E)
    (S : Finset (Fin (2*r))) (hS : halfTurnSupport S = S) :
    (tensorModel e S).Equiv
      ((tensorModel e (halfSupport S)).tprod
        ((tensorModel e (halfSupport S)).comp (graphDerived F ^ r).toMonoidHom)) := by
  apply Representation.Equiv.symm
  refine .mk (pairedCoordinates S hS) ?_
  intro g
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  funext x
  change pairedCoordinates S hS
      (tensorModel e (halfSupport S) g v ⊗ₜ[E]
        tensorModel e (halfSupport S) ((graphDerived F ^ r) g) w) x =
    (tensorMatrix e S g).mulVec (pairedCoordinates S hS (v ⊗ₜ[E] w)) x
  simp only [pairedCoordinates_tmul]
  change (∑ a, tensorMatrix e (halfSupport S) g (pairedIndex S hS x).1 a * v a) *
    (∑ b, tensorMatrix e (halfSupport S) ((graphDerived F ^ r) g)
      (pairedIndex S hS x).2 b * w b) = _
  simp only [Matrix.mulVec, dotProduct, tensorMatrix_pair hF e S hS, pairedCoordinates_tmul]
  rw [← (pairedIndex S hS).symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A nonempty invariant support has a nonempty first half. -/
theorem halfSupport_nonempty (S : Finset (Fin (2*r))) (hS : halfTurnSupport S = S)
    (hne : S.Nonempty) : (halfSupport S).Nonempty := by
  obtain ⟨j, hj⟩ := hne
  by_cases hl : j.val < r
  · exact ⟨j, Finset.mem_filter.mpr ⟨hj, hl⟩⟩
  · exact ⟨j + (r : Fin (2*r)), Finset.mem_filter.mpr
      ⟨(shift_mem S hS j).mpr hj, (shift_low_iff j).mpr hl⟩⟩

end
end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
