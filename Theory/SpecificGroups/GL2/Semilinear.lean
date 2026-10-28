module
public import Theory.SpecificGroups.GL2.DeterminantTwoPower
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The actual semilinear GL2 group

Coefficient-ring automorphisms act entrywise on invertible two-by-two
matrices. Their semidirect product with GL2 is the concrete GammaL2 model.
The canonical pure coefficient elements conjugate the GL2 layer by precisely
that coefficient map, and every determinant two-power level has normal
image in GammaL2.

The coefficient action is built from the existing matrix map. Its invariance
of determinant levels is the proved determinant/coefficient compatibility.
Conjugation in the semidirect product is a coefficient action followed by
inner conjugation in GL2, which proves normality of each exact source level.

This supplies the linear semilinear model and invariance step in ABG II.3
Proposition 3, article pp.24--27. Over a finite field the coefficient group
is its actual Galois automorphism group; no abstract action or ambient
recognition conclusion is assumed.
-/

namespace Matrix.GeneralLinearGroup

@[expose] public def coefficientEquiv {F K : Type*} [CommRing F] [CommRing K]
    (e : F ≃+* K) : GL (Fin 2) F ≃* GL (Fin 2) K where
  toFun := map e.toRingHom
  invFun := map e.symm.toRingHom
  left_inv A := by ext i j; exact e.symm_apply_apply (A i j)
  right_inv A := by ext i j; exact e.apply_symm_apply (A i j)
  map_mul' A B := (map e.toRingHom).map_mul A B

@[expose] public def coefficientAction (F : Type*) [CommRing F] :
    (F ≃+* F) →* MulAut (GL (Fin 2) F) where
  toFun := coefficientEquiv
  map_one' := by ext A i j; rfl
  map_mul' e f := by ext A i j; rfl

public abbrev GammaL2 (F : Type*) [CommRing F] :=
  GL (Fin 2) F ⋊[coefficientAction F] (F ≃+* F)

public theorem coefficientAction_mem_determinantTwoPower_iff
    (F : Type*) [CommRing F] (m : ℕ) (e : F ≃+* F) (A : GL (Fin 2) F) :
    coefficientAction F e A ∈ determinantTwoPower F m ↔ A ∈ determinantTwoPower F m :=
  determinantTwoPower_mem_map_iff e m A

public theorem gammaL2_inr_conj_inl
    (F : Type*) [CommRing F] (e : F ≃+* F) (A : GL (Fin 2) F) :
    (SemidirectProduct.inr e : GammaL2 F) * SemidirectProduct.inl A *
      (SemidirectProduct.inr e)⁻¹ = SemidirectProduct.inl (map e.toRingHom A) := by
  change (SemidirectProduct.inr e : GammaL2 F) * SemidirectProduct.inl A *
    (SemidirectProduct.inr e)⁻¹ = SemidirectProduct.inl (coefficientAction F e A)
  rw [← map_inv]
  exact (SemidirectProduct.inl_aut (φ := coefficientAction F) e A).symm

public theorem determinantTwoPower_semilinear_normal
    (F : Type*) [CommRing F] (m : ℕ) :
    ((determinantTwoPower F m).map (SemidirectProduct.inl : GL (Fin 2) F →* GammaL2 F)).Normal := by
  let D := determinantTwoPower F m
  constructor
  rintro x ⟨A, hA, rfl⟩ g
  have hfield : coefficientAction F g.right A ∈ D :=
    (coefficientAction_mem_determinantTwoPower_iff F m g.right A).mpr hA
  have hinner : g.left * coefficientAction F g.right A * g.left⁻¹ ∈ D :=
    (inferInstance : D.Normal).conj_mem _ hfield g.left
  refine ⟨_, hinner, ?_⟩
  apply SemidirectProduct.ext
  · simp
  · simp

end Matrix.GeneralLinearGroup

