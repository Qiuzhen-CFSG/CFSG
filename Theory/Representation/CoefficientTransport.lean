module

public import Theory.Representation.Quotient
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Coefficient transport of matrix representations

A field isomorphism acts coordinatewise on a standard vector space.
Semilinear conjugation then transports representations without changing their
dimension or invariant-subspace lattice. On matrices this applies the field
isomorphism to every entry, so characteristic polynomials are transported
coefficientwise as well.

This extends the coefficient-automorphism construction in
`Theory.Representation.SemilinearConjugation` to two different fields and
records characteristic polynomials, rather than only traces. It supplies
actual representation transport between compatible modular splitting fields;
root multiplicities can consequently be compared for Brauer characters.
-/

public section
noncomputable section
namespace Representation
variable {K L G : Type*} [Field K] [Field L] [Group G]
variable (e : K ≃+* L)
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The coordinatewise semilinear equivalence induced by the field isomorphism. -/
@[expose] def coefficientEquiv (m : ℕ) :
    LinearEquiv (e : K →+* L) (σ' := (e.symm : L →+* K)) (Fin m → K) (Fin m → L) where
  toFun v i := e (v i)
  invFun v i := e.symm (v i)
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp

/-- Transport all action matrices to the new coefficient field. -/
@[expose] def changeCoefficients {m : ℕ} (ρ : Representation K G (Fin m → K)) :
    Representation L G (Fin m → L) :=
  (coefficientEquiv e m).conjRingEquiv.toMonoidHom.comp ρ

@[simp] theorem changeCoefficients_apply {m : ℕ} (ρ : Representation K G (Fin m → K))
    (g : G) (v : Fin m → L) (i : Fin m) :
    changeCoefficients e ρ g v i = e (ρ g (fun j => e.symm (v j)) i) := rfl

/-- Coefficient transport preserves the lattice of invariant subspaces. -/
@[expose] def changeCoefficientsSubrepresentationOrderIso {m : ℕ}
    (ρ : Representation K G (Fin m → K)) :
    Subrepresentation ρ ≃o Subrepresentation (changeCoefficients e ρ) where
  toFun S :=
    { toSubmodule := S.toSubmodule.comap (coefficientEquiv e m).symm.toLinearMap
      apply_mem_toSubmodule g v hv := by
        change (coefficientEquiv e m).symm
          ((coefficientEquiv e m) (ρ g ((coefficientEquiv e m).symm v))) ∈ S.toSubmodule
        simpa using S.apply_mem_toSubmodule g hv }
  invFun S :=
    { toSubmodule := S.toSubmodule.comap (coefficientEquiv e m).toLinearMap
      apply_mem_toSubmodule g v hv := by
        have h := S.apply_mem_toSubmodule g hv
        change (coefficientEquiv e m)
          (ρ g ((coefficientEquiv e m).symm ((coefficientEquiv e m) v))) ∈ S.toSubmodule at h
        simpa using h }
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    simp
  right_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    simp
  map_rel_iff' := by
    intro S T
    change (∀ v, (coefficientEquiv e m).symm v ∈ S.toSubmodule →
      (coefficientEquiv e m).symm v ∈ T.toSubmodule) ↔ S ≤ T
    constructor
    · intro h v hv
      have hv' : v ∈ S.toSubmodule := hv
      have ht := h ((coefficientEquiv e m) v) (by simpa using hv')
      change v ∈ T.toSubmodule
      simpa using ht
    · intro h v hv
      exact h hv

theorem changeCoefficients_irreducible_iff {m : ℕ}
    (ρ : Representation K G (Fin m → K)) :
    IsIrreducible (changeCoefficients e ρ) ↔ IsIrreducible ρ :=
  (changeCoefficientsSubrepresentationOrderIso e ρ).isSimpleOrder_iff.symm

theorem changeCoefficients_toMatrix {m : ℕ}
    (ρ : Representation K G (Fin m → K)) (g : G) :
    LinearMap.toMatrix' (changeCoefficients e ρ g) = (LinearMap.toMatrix' (ρ g)).map e := by
  ext i j
  simp only [LinearMap.toMatrix'_apply, changeCoefficients_apply, Matrix.map_apply]
  have hsingle : (fun k => e.symm ((Pi.single j (1 : L) : Fin m → L) k)) =
      (Pi.single j (1 : K) : Fin m → K) := by
    funext k
    simp [Pi.single_apply]
  rw [hsingle]

theorem changeCoefficients_charpoly {m : ℕ}
    (ρ : Representation K G (Fin m → K)) (g : G) :
    (changeCoefficients e ρ g).charpoly = (ρ g).charpoly.map (e : K →+* L) := by
  rw [← LinearMap.charpoly_toMatrix (changeCoefficients e ρ g) (Pi.basisFun L (Fin m)),
    ← LinearMap.charpoly_toMatrix (ρ g) (Pi.basisFun K (Fin m))]
  change (LinearMap.toMatrix' (changeCoefficients e ρ g)).charpoly =
    (LinearMap.toMatrix' (ρ g)).charpoly.map (e : K →+* L)
  rw [changeCoefficients_toMatrix]
  exact Matrix.charpoly_map (LinearMap.toMatrix' (ρ g)) (e : K →+* L)

@[simp] theorem changeCoefficients_symm {m : ℕ}
    (ρ : Representation K G (Fin m → K)) :
    changeCoefficients e.symm (changeCoefficients e ρ) = ρ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  funext i
  simp only [changeCoefficients_apply, RingEquiv.symm_symm,
    RingEquiv.symm_apply_apply]

@[simp] theorem changeCoefficients_comp {H : Type*} [Group H] {m : ℕ}
    (ρ : Representation K G (Fin m → K)) (π : H →* G) :
    changeCoefficients e (ρ.comp π) = (changeCoefficients e ρ).comp π := rfl

/-- Transport a genuine representation isomorphism to the new coefficient field. -/
def changeCoefficientsEquiv {m n : ℕ} {ρ : Representation K G (Fin m → K)}
    {σ : Representation K G (Fin n → K)} (f : ρ.Equiv σ) :
    (changeCoefficients e ρ).Equiv (changeCoefficients e σ) := by
  let E : (Fin m → L) ≃ₗ[L] (Fin n → L) :=
    ((coefficientEquiv e m).symm.trans f.toLinearEquiv).trans (coefficientEquiv e n)
  refine .mk E ?_
  intro g
  apply LinearMap.ext
  intro v
  funext i
  have hf := congrArg (fun T : (Fin m → K) →ₗ[K] (Fin n → K) =>
    e (T (fun j => e.symm (v j)) i)) (f.isIntertwining' g)
  simpa [E, coefficientEquiv, changeCoefficients_apply] using hf

/-- The group-algebra action commutes with coefficient transport. -/
theorem changeCoefficients_asAlgebraHom {m : ℕ}
    (ρ : Representation K G (Fin m → K)) (a : MonoidAlgebra K G) :
    (changeCoefficients e ρ).asAlgebraHom (MonoidAlgebra.mapRingHom G (e : K →+* L) a) =
      (coefficientEquiv e m).conjRingEquiv (ρ.asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r =>
    simp only [MonoidAlgebra.mapRingHom_single, asAlgebraHom_single]
    apply LinearMap.ext
    intro v
    funext i
    change e r * e (ρ g (fun j => e.symm (v j)) i) =
      e (r * ρ g (fun j => e.symm (v j)) i)
    exact (map_mul e _ _).symm

end Representation
