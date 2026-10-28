module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Models
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Construction
public import Theory.Representation.CoefficientReduction
public import Theory.Representation.ExtendScalars

/-!
# Concrete tensor models for nonbinary symplectic-four recognition

Let D be the literal derived subgroup of Sp₄(F). Restrict the exceptional
matrix automorphism to its characteristic derived subgroup. Its square is
entrywise Frobenius, so the powers with exponents 2i and 2i+1 give the
Frobenius twists of the two four-dimensional basic modules.

For a subset S of {0,...,2n-1}, `tensorModel e S` is the corresponding tensor
representation in its coordinate basis, with coefficients embedded by e.
The product-of-entries formula proves the representation laws directly.
Its degree is 4^|S|. For singleton S, an explicit coordinate equivalence
intertwines the tensor action with the basic twist. Restriction to F₂ and
the actual graph automorphism give natural-module quasiequivalence.

`AbsoluteTensorCatalogue` specifies the still-unproved irreducibility,
inequivalence and exhaustivity of these concrete models. No inhabitant of
that specification is asserted here, nor is every binary irreducible claimed
to be a restriction of one of these F-modules.

Sources: GLS3, 2.8.6(a), 2.8.8 and Examples 2.8.10(d),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher--Smith, G.9.3 proof,
printed pp.356--357 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
namespace Nonbinary

open Representation
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

/-- The group in G.9.3(9), without changing its matrix carrier. -/
abbrev Derived (F : Type*) [Field F] := commutator (Matrix.symplecticGroup (Fin 2) F)
/-- The ordered four coordinates of the natural symplectic module. -/
abbrev Coordinate := Fin 2 ⊕ Fin 2

variable (F : Type*) [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- Restrict the actual exceptional automorphism to the characteristic derived subgroup. -/
noncomputable def graphDerived : MulAut (Derived F) := by
  letI : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  exact MulAut.characteristic _ (ExceptionalGraph.graphAut (F := F))

/-- Exponents 2i and 2i+1 give the natural and graph-twisted basic factors. -/
noncomputable def basicTwist (j : ℕ) : Representation F (Derived F) (Coordinate → F) :=
  (symplecticDerivedNatural 2).comp (graphDerived F ^ j).toMonoidHom

/-- The group isomorphism is the specified graph power and the linear map is identity. -/
theorem basicTwist_quasiequivalent (j : ℕ) :
    Quasiequivalent (restrictScalars (k := ZMod 2) (basicTwist F j)) (binaryNatural F) := by
  exact ⟨graphDerived F ^ j, LinearEquiv.refl _ _, fun _ _ => rfl⟩

/-- The exceptional square remains entrywise Frobenius on the actual derived group. -/
theorem graphDerived_square_apply (g : Derived F) (i j : Coordinate) :
    ((graphDerived F ^ 2) g).val.val i j = (g.val.val i j) ^ 2 := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have h := congrArg
    (fun a : MulAut (Matrix.symplecticGroup (Fin 2) F) => (a g.val).val i j)
    (ExceptionalGraph.graphAut_square (F := F))
  exact h

variable {F} {E : Type*} [Field E]

/-- Matrices of the tensor action in the tensor-product coordinate basis. -/
def tensorMatrix {n : ℕ} (e : F →+* E) (S : Finset (Fin (2*n)))
    (g : Derived F) : Matrix (S → Coordinate) (S → Coordinate) E :=
  fun x y => ∏ j : S, e (((graphDerived F ^ (j.val : ℕ)) g).val.val (x j) (y j))

private theorem tensorMatrix_one {n : ℕ} (e : F →+* E) (S : Finset (Fin (2*n))) :
    tensorMatrix e S 1 = 1 := by
  classical
  have hm (j : S) : ((graphDerived F ^ (j.val : ℕ)) (1 : Derived F)).val.val =
      (1 : Matrix Coordinate Coordinate F) :=
    congrArg (fun g : Derived F => g.val.val) (map_one (graphDerived F ^ (j.val : ℕ)))
  ext x y
  simp_rw [tensorMatrix, hm]
  simp only [Matrix.one_apply, apply_ite e, map_one, map_zero]
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one, ← funext_iff]

private theorem tensorMatrix_mul {n : ℕ} (e : F →+* E) (S : Finset (Fin (2*n)))
    (g h : Derived F) : tensorMatrix e S (g*h) = tensorMatrix e S g * tensorMatrix e S h := by
  classical
  have hm (j : S) : ((graphDerived F ^ (j.val : ℕ)) (g*h)).val.val =
      ((graphDerived F ^ (j.val : ℕ)) g).val.val *
        ((graphDerived F ^ (j.val : ℕ)) h).val.val :=
    congrArg (fun g : Derived F => g.val.val) (map_mul (graphDerived F ^ (j.val : ℕ)) g h)
  ext x z
  simp_rw [tensorMatrix, hm]
  simp only [Matrix.mul_apply, map_sum, map_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.prod_mul_distrib

/-- The actual action, including both basic factors at each Frobenius position. -/
noncomputable def tensorModel {n : ℕ} (e : F →+* E) (S : Finset (Fin (2*n))) :
    Representation E (Derived F) ((S → Coordinate) → E) where
  toFun g := (tensorMatrix e S g).mulVecLin
  map_one' := by rw [tensorMatrix_one, Matrix.mulVecLin_one]; rfl
  map_mul' g h := by rw [tensorMatrix_mul, Matrix.mulVecLin_mul]; rfl

/-- The coordinate dimension of the concrete tensor model. -/
theorem tensorModel_finrank {n : ℕ} (S : Finset (Fin (2*n))) :
    Module.finrank E ((S → Coordinate) → E) = 4 ^ S.card := by
  simp [Coordinate]

/-- Evaluate the singleton-indexed coordinate at its unique element. -/
noncomputable def singletonCoordinates {n : ℕ} (j : Fin (2*n)) :
    ((({j} : Finset (Fin (2*n))) → Coordinate) → E) ≃ₗ[E] (Coordinate → E) :=
  LinearEquiv.funCongrLeft E E (Equiv.funUnique ({j} : Finset (Fin (2*n))) Coordinate).symm

/-- An intertwining equivalence identifies a one-factor tensor with its basic twist. -/
noncomputable def tensorModel_singleton_equiv {n : ℕ} (e : F →+* E) (j : Fin (2*n)) :
    (tensorModel e {j}).Equiv (mapCoefficients e (basicTwist F j)) := by
  refine .mk (singletonCoordinates j) ?_
  intro g
  apply LinearMap.ext
  intro v
  funext i
  change (∑ y, tensorMatrix e {j} g (fun _ => i) y * v y) = _
  have hm : LinearMap.toMatrix' (basicTwist F j g) =
      ((graphDerived F ^ (j : ℕ)) g).val.val :=
    LinearMap.toMatrix'_toLin' _
  change _ = ((LinearMap.toMatrix' (basicTwist F j g)).map e).mulVec
    (fun k => v (fun _ => k)) i
  rw [hm]
  simp only [tensorMatrix, Fintype.prod_unique,
    Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact ((Equiv.funUnique ({j} : Finset (Fin (2*n))) Coordinate).symm.sum_comp
    (fun y => e (((graphDerived F ^ (j : ℕ)) g).val.val i (y ⟨j, by simp⟩)) * v y)).symm

/-- A one-factor tensor over F restricts to the binary natural module up to quasiequivalence. -/
theorem tensorModel_singleton_quasiequivalent {n : ℕ} (j : Fin (2*n)) :
    Quasiequivalent (restrictScalars (k := ZMod 2) (tensorModel (RingHom.id F) {j}))
      (binaryNatural F) := by
  have he : mapCoefficients (RingHom.id F) (basicTwist F j) = basicTwist F j := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.toMatrix'.injective
    simp only [mapCoefficients_toMatrix, RingHom.coe_id, Matrix.map_id]
  let φ := tensorModel_singleton_equiv (RingHom.id F) j
  rw [he] at φ
  refine ⟨graphDerived F ^ (j : ℕ), φ.toLinearEquiv.restrictScalars (ZMod 2), ?_⟩
  intro g v
  exact IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v

/-- Scalar restriction multiplies the tensor degree by the defining-field degree. -/
theorem tensorModel_binary_finrank {n : ℕ} (hF : Nat.card F = 2^n)
    (S : Finset (Fin (2*n))) :
    Module.finrank (ZMod 2) ((S → Coordinate) → F) = n * 4^S.card := by
  let : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  rw [← Module.finrank_mul_finrank (ZMod 2) F ((S → Coordinate) → F),
    tensorModel_finrank, Representation.OneCohomology.coefficient_finrank_of_card 2 n hF]

universe u v

/-- The explicit absolute tensor classification still needed from GLS 2.8.6(a).
This is a specification, not an asserted classification theorem. -/
structure AbsoluteTensorCatalogue
    (F : Type u) [Field F] [Finite F] [Algebra (ZMod 2) F]
    (E : Type v) [Field E] [IsAlgClosed E] (e : F →+* E) (n : ℕ) : Prop where
  irreducible : ∀ S : Finset (Fin (2*n)), IsIrreducible (tensorModel e S)
  distinguish : ∀ S T : Finset (Fin (2*n)),
    Nonempty ((tensorModel e S).Equiv (tensorModel e T)) → S = T
  exhaustive : ∀ (W : Type v) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (ρ : Representation E (Derived F) W), IsIrreducible ρ →
      ∃ S : Finset (Fin (2*n)), Nonempty (ρ.Equiv (tensorModel e S))

end Nonbinary
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
