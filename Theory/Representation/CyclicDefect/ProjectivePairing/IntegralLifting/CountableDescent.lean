module

public import Theory.Representation.CyclicDefect.ProjectivePairing.LiftContracts
public import Theory.Representation.CyclicDefect.ProjectivePairing.Projectivity
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.SetTheory.Cardinal.Subfield

/-!
# Countable coefficient descent of projective representations

A finite-dimensional representation of a finite group and its projectivity
norm witness use finitely many matrix entries. Take the subfield generated
by those entries and the chosen modular root, then its relative algebraic
closure. This remains countable. The action and norm identity descend
entrywise, so the resulting coordinate representation is genuinely projective.
An intertwining equivalence transports the construction to arbitrary finite
vector spaces, in particular the linear-Hom representation in tensor pairings.

This supplies the coefficient-size reduction before the complete-local-ring
construction of Feit, *The Representation Theory of Finite Groups*, I.12--13
and I.17. It does not assert existence of an integral lift.
-/

public section
noncomputable section
open scoped BigOperators
namespace Representation.CyclicDefect.ProjectivePairing.IntegralLifting
variable {K G : Type*} [Field K] [Group G] [Fintype G]

private theorem countable_closed_subfield [IsAlgClosed K]
    (s : Set K) (hs : s.Countable) :
    ∃ k : Subfield K, Countable k ∧ IsAlgClosed k ∧ s ⊆ k := by
  let k₀ := Subfield.closure s
  have : Countable k₀ := Cardinal.mk_le_aleph0_iff.mp
    ((Subfield.cardinalMk_closure_le_max s).trans (max_le hs.le_aleph0 le_rfl))
  refine ⟨(algebraicClosure k₀ K).toSubfield, ?_, ?_, ?_⟩
  · change Countable (algebraicClosure k₀ K)
    exact Cardinal.mk_le_aleph0_iff.mp
      ((Algebra.IsAlgebraic.cardinalMk_le_max k₀ (algebraicClosure k₀ K)).trans (by simp))
  · change IsAlgClosed (algebraicClosure k₀ K)
    exact (algebraicClosure.isAlgClosure k₀ K).isAlgClosed
  · intro x hx
    exact IntermediateField.algebraMap_mem (algebraicClosure k₀ K)
      (⟨x, Subfield.subset_closure hx⟩ : k₀)

variable {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Genuine projectivity is invariant under an intertwining equivalence. -/
theorem projective_equiv {ρ : Representation K G V} {σ : Representation K G W}
    (e : ρ.Equiv σ) [Module.Projective (MonoidAlgebra K G) ρ.asModule] :
    Module.Projective (MonoidAlgebra K G) σ.asModule := by
  obtain ⟨θ, hθ⟩ := exists_norm ρ
  apply Representation.ProjectiveTrace.projective_of_norm σ (e.toLinearEquiv.conj θ)
  intro v
  apply e.toLinearEquiv.symm.injective
  have hs (g : G) (w : W) : e.toLinearEquiv.symm (σ g w) = ρ g (e.toLinearEquiv.symm w) :=
    LinearMap.congr_fun (e.symm.toIntertwiningMap.isIntertwining' g) w
  simpa only [map_sum, hs, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply] using hθ (e.toLinearEquiv.symm v)

/-- Put the representation in finite coordinates. -/
def coordinates [FiniteDimensional K V] (Q : Representation K G V) :
    Representation K G (Fin (Module.finrank K V) → K) :=
  (Module.finBasis K V).equivFun.conjRingEquiv.toMonoidHom.comp Q

/-- The finite coordinate representation is equivalent to the original one. -/
def coordinatesEquiv [FiniteDimensional K V] (Q : Representation K G V) :
    (coordinates Q).Equiv Q := by
  refine .mk (Module.finBasis K V).equivFun.symm ?_
  intro g
  apply LinearMap.ext
  intro v
  change (Module.finBasis K V).equivFun.symm
    ((Module.finBasis K V).equivFun (Q g ((Module.finBasis K V).equivFun.symm v))) = _
  simp

private theorem descend_matrices {n : ℕ} (Q : Representation K G (Fin n → K))
    (θ : Module.End K (Fin n → K))
    (hθ : ∀ v, ∑ g : G, Q g⁻¹ (θ (Q g v)) = v)
    (k : Subfield K)
    (hQ : ∀ g i j, LinearMap.toMatrix' (Q g) i j ∈ k)
    (hB : ∀ i j, LinearMap.toMatrix' θ i j ∈ k) :
    ∃ τ : Representation k G (Fin n → k),
      Module.Projective (MonoidAlgebra k G) τ.asModule ∧
      mapCoefficients k.subtype τ = Q := by
  classical
  let M (g : G) : Matrix (Fin n) (Fin n) k :=
    fun i j => ⟨LinearMap.toMatrix' (Q g) i j, hQ g i j⟩
  let B : Matrix (Fin n) (Fin n) k :=
    fun i j => ⟨LinearMap.toMatrix' θ i j, hB i j⟩
  let f : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) K := k.subtype.mapMatrix
  have hf : Function.Injective f := Matrix.map_injective Subtype.val_injective
  have hM (g : G) : f (M g) = LinearMap.toMatrix' (Q g) := rfl
  have hB' : f B = LinearMap.toMatrix' θ := rfl
  let μ : G →* Matrix (Fin n) (Fin n) k :=
    { toFun := M
      map_one' := hf (by rw [hM, map_one, LinearMap.toMatrix'_one, map_one])
      map_mul' := fun g h => hf (by rw [hM, Q.map_mul, LinearMap.toMatrix'_mul, f.map_mul, hM, hM]) }
  let τ : Representation k G (Fin n → k) := Matrix.toLinAlgEquiv'.toMonoidHom.comp μ
  have hτ (g : G) : LinearMap.toMatrix' (τ g) = M g :=
    LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _
  have hnorm : ∑ g : G, M g⁻¹ * B * M g = 1 := by
    apply hf
    rw [map_sum, map_one]
    simp only [map_mul, hM, hB']
    have he : ∑ g : G, Q g⁻¹ * θ * Q g = 1 := by
      apply LinearMap.ext
      intro v
      simpa only [LinearMap.sum_apply, Module.End.mul_apply, Module.End.one_apply] using hθ v
    simpa only [map_sum, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_one] using
      congrArg LinearMap.toMatrix' he
  refine ⟨τ, ?_, ?_⟩
  · apply Representation.ProjectiveTrace.projective_of_norm τ (Matrix.toLin' B)
    have he : ∑ g : G, τ g⁻¹ * Matrix.toLin' B * τ g = 1 := by
      apply LinearMap.toMatrix'.injective
      simpa only [map_sum, LinearMap.toMatrix'_mul, hτ,
        LinearMap.toMatrix'_one, LinearMap.toMatrix'_toLin'] using hnorm
    intro v
    simpa only [LinearMap.sum_apply, Module.End.mul_apply, Module.End.one_apply] using
      LinearMap.congr_fun he v
  · apply MonoidHom.ext
    intro g
    apply LinearMap.toMatrix'.injective
    rw [mapCoefficients_toMatrix, hτ]
    exact hM g

/-- A finite projective representation descends to a countable algebraically closed
subfield containing any prescribed coefficient. Projectivity descends together
with its norm witness. -/
theorem exists_countable_model [IsAlgClosed K] [FiniteDimensional K V]
    (Q : Representation K G V)
    [Module.Projective (MonoidAlgebra K G) Q.asModule] (z : K) :
    ∃ (k : Subfield K), Countable k ∧ IsAlgClosed k ∧ z ∈ k ∧
      ∃ (n : ℕ) (τ : Representation k G (Fin n → k)),
        Module.Projective (MonoidAlgebra k G) τ.asModule ∧
        Nonempty ((mapCoefficients k.subtype τ).Equiv Q) := by
  classical
  let Q' := coordinates Q
  have : Module.Projective (MonoidAlgebra K G) Q'.asModule :=
    projective_equiv (coordinatesEquiv Q).symm
  obtain ⟨θ, hθ⟩ := exists_norm Q'
  let s : Set K := {z} ∪
    Set.range (fun t : G × Fin (Module.finrank K V) × Fin (Module.finrank K V) =>
      LinearMap.toMatrix' (Q' t.1) t.2.1 t.2.2) ∪
    Set.range (fun t : Fin (Module.finrank K V) × Fin (Module.finrank K V) =>
      LinearMap.toMatrix' θ t.1 t.2)
  have hs : s.Countable := (Set.countable_singleton z |>.union
    (Set.toFinite _).countable).union (Set.toFinite _).countable
  obtain ⟨k, hk, ha, hs⟩ := countable_closed_subfield s hs
  have hQ : ∀ g i j, LinearMap.toMatrix' (Q' g) i j ∈ k :=
    fun g i j => hs (Or.inl (Or.inr ⟨(g, i, j), rfl⟩))
  have hB : ∀ i j, LinearMap.toMatrix' θ i j ∈ k :=
    fun i j => hs (Or.inr ⟨(i, j), rfl⟩)
  obtain ⟨τ, hτ, he⟩ := descend_matrices Q' θ hθ k hQ hB
  refine ⟨k, hk, ha, hs (Or.inl (Or.inl rfl)), _, τ, hτ, ?_⟩
  rw [he]
  exact ⟨coordinatesEquiv Q⟩

/-- Restrict the chosen root correspondence to a subfield containing its modular root. -/
def rootLiftOn {m : ℕ} (L : CyclicRootLift K m) (k : Subfield K)
    (hz : L.modularRoot ∈ k) : CyclicRootLift k m where
  positive := L.positive
  modularRoot := ⟨L.modularRoot, hz⟩
  complexRoot := L.complexRoot
  modular_primitive := IsPrimitiveRoot.of_map_of_injective
    (f := k.subtype) L.modular_primitive Subtype.val_injective
  complex_primitive := L.complex_primitive

/-- The literal tensor-pairing consumer has a countable projective model.
This uses the proved projectivity of `linHom`, without a semisimplicity assumption. -/
theorem exists_countable_linHom_model [IsAlgClosed K]
    [FiniteDimensional K V] [FiniteDimensional K W]
    {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    {m : ℕ} (L : CyclicRootLift K m)
    (P : Representation K G U) (ρ : Representation K G V) (σ : Representation K G W)
    [Module.Projective (MonoidAlgebra K G) P.asModule] :
    ∃ (k : Subfield K), Countable k ∧ IsAlgClosed k ∧ L.modularRoot ∈ k ∧
      ∃ (n : ℕ) (τ : Representation k G (Fin n → k)),
        Module.Projective (MonoidAlgebra k G) τ.asModule ∧
        Nonempty ((mapCoefficients k.subtype τ).Equiv (linHom P (ρ.tprod σ))) := by
  have : Module.Projective (MonoidAlgebra K G) (linHom P (ρ.tprod σ)).asModule :=
    projective_linHom P (ρ.tprod σ)
  exact exists_countable_model (linHom P (ρ.tprod σ)) L.modularRoot

end Representation.CyclicDefect.ProjectivePairing.IntegralLifting
