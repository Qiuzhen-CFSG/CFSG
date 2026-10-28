module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Assembly
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Left HS actions from marked row sections

Let `N` be the kernel rows and `U` the lifted rows of a marked section of an
actual HS representation. The identities `N T = K N` and `U T = C N + M U`
make `ker N` invariant and make multiplication by `U` intertwine the restricted
action with `M`. If this map is surjective, its kernel quotient carries an actual
left action in the required target coordinates. This annihilator quotient is
the dual of the supplied right row subquotient; it retains the raw matrices `M`.

Invariance under the two literal permutation generators extends to the whole
carrier using its finiteness and generation, with no order or simplicity claim.
A right inverse to the stacked rows discharges the linear surjectivity premise.
The applications return the exact `Binary.MarkedAction` consumed by the model
assembly. The concrete tensor or exterior-square actions and the numerical
identities remain explicit inputs to these structural descent lemmas.

Source: the HS section certificates and conventions in `Binary/source/README.md`,
from R. A. Wilson et al., ATLAS of Finite Group Representations.
-/

@[expose] public section

namespace Representation.HigmanSims.LargeModels.Binary.Large.Descent
open Sporadic.LeechRelated.HS

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem invariant_of_generators (ρ : Representation k Carrier V) (U : Submodule k V)
    (ha : ∀ x ∈ U, ρ permutationA x ∈ U)
    (hb : ∀ x ∈ U, ρ permutationB x ∈ U) :
    ∀ g, U ≤ U.comap (ρ g) := by
  let S : Submonoid Carrier :=
    { carrier := {g | ∀ x ∈ U, ρ g x ∈ U}
      one_mem' := by intro x hx; simpa using hx
      mul_mem' := by
        intro g h hg hh x hx
        simpa only [map_mul, Module.End.mul_apply] using hg _ (hh x hx) }
  have hle : Submonoid.closure ({permutationA, permutationB} : Set Carrier) ≤ S := by
    apply Submonoid.closure_le.mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact ha
    · exact Set.mem_singleton_iff.mp hg ▸ hb
  have htop : Subgroup.closure ({permutationA, permutationB} : Set Carrier) = ⊤ := by
    apply eq_top_of_generators_mem
    · exact Subgroup.subset_closure (by simp [permutationA, generatorAElement])
    · exact Subgroup.subset_closure (by simp [permutationB, generatorBElement])
  intro g x hx
  have hg : g ∈ Submonoid.closure ({permutationA, permutationB} : Set Carrier) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite, htop]
    trivial
  exact hle hg x hx

variable {W : Type*} [AddCommGroup W] [Module k W]

noncomputable def quotientAction (ρ : Representation k Carrier V) (q : V →ₗ[k] W)
    (hq : Function.Surjective q) (hstable : ∀ g, q.ker ≤ q.ker.comap (ρ g)) :
    Representation k Carrier W :=
  (q.quotKerEquivOfSurjective hq).conjRingEquiv.toMonoidHom.comp (ρ.quotient q.ker hstable)

theorem quotientAction_apply (ρ : Representation k Carrier V) (q : V →ₗ[k] W)
    (hq : Function.Surjective q) (hstable : ∀ g, q.ker ≤ q.ker.comap (ρ g))
    (g : Carrier) (x : V) :
    quotientAction ρ q hq hstable g (q x) = q (ρ g x) := by
  simp [quotientAction, LinearEquiv.conjRingEquiv, Representation.quotient,
    Submodule.mapQ_apply]

theorem exists_quotientAction_of_generators (ρ : Representation k Carrier V)
    (q : V →ₗ[k] W) (hq : Function.Surjective q) (A B : Module.End k W)
    (ha : ∀ x, q (ρ permutationA x) = A (q x))
    (hb : ∀ x, q (ρ permutationB x) = B (q x)) :
    ∃ σ : Representation k Carrier W,
      (∀ g x, σ g (q x) = q (ρ g x)) ∧ σ permutationA = A ∧ σ permutationB = B := by
  have hs : ∀ g, q.ker ≤ q.ker.comap (ρ g) := by
    apply invariant_of_generators
    · intro x hx
      change q (ρ permutationA x) = 0
      rw [ha, LinearMap.mem_ker.mp hx, map_zero]
    · intro x hx
      change q (ρ permutationB x) = 0
      rw [hb, LinearMap.mem_ker.mp hx, map_zero]
  refine ⟨quotientAction ρ q hq hs, quotientAction_apply ρ q hq hs, ?_, ?_⟩
  · ext y
    obtain ⟨x, rfl⟩ := hq y
    exact (quotientAction_apply ρ q hq hs _ x).trans (ha x)
  · ext y
    obtain ⟨x, rfl⟩ := hq y
    exact (quotientAction_apply ρ q hq hs _ x).trans (hb x)

/-- Kernel rows followed by lifted rows, without changing their coordinates. -/
def stackedRows {m r n : ℕ} (N : Matrix (Fin r) (Fin m) (ZMod 2))
    (U : Matrix (Fin n) (Fin m) (ZMod 2)) :
    Matrix (Fin r ⊕ Fin n) (Fin m) (ZMod 2) := Sum.elim N U

/-- A right inverse to the stacked rows supplies the surjectivity needed by
annihilator-quotient descent. The kernel rows precede the lifted rows. -/
theorem rowSubquotient_surjective_of_rightInverse {m r n : ℕ}
    (N : Matrix (Fin r) (Fin m) (ZMod 2))
    (U : Matrix (Fin n) (Fin m) (ZMod 2))
    (R : Matrix (Fin m) (Fin r ⊕ Fin n) (ZMod 2))
    (hR : stackedRows N U * R = 1) :
    ∀ y : Fin n → ZMod 2, ∃ x, N.mulVec x = 0 ∧ U.mulVec x = y := by
  intro y
  let z : Fin r ⊕ Fin n → ZMod 2 := Sum.elim 0 y
  have hz : (stackedRows N U).mulVec (R.mulVec z) = z := by
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  refine ⟨R.mulVec z, ?_, ?_⟩
  · funext j
    exact congrFun hz (Sum.inl j)
  · funext j
    exact congrFun hz (Sum.inr j)

/-- Generator identities for rows produce an actual marked left action on the
annihilator quotient. The map from `ker N` to the target is multiplication by U.
Surjectivity identifies its kernel quotient with the required coordinate space. -/
theorem markedAction_of_rowSubquotient (i : Fin 4) (m r : ℕ)
    (ρ : Representation (ZMod 2) Carrier (Fin m → ZMod 2))
    (N : Matrix (Fin r) (Fin m) (ZMod 2))
    (U : Matrix (Fin (binaryDegree i)) (Fin m) (ZMod 2))
    (Ka Kb : Matrix (Fin r) (Fin r) (ZMod 2))
    (Ca Cb : Matrix (Fin (binaryDegree i)) (Fin r) (ZMod 2))
    (hNa : N * LinearMap.toMatrix' (ρ permutationA) = Ka * N)
    (hNb : N * LinearMap.toMatrix' (ρ permutationB) = Kb * N)
    (hUa : U * LinearMap.toMatrix' (ρ permutationA) = Ca * N + aMatrix i * U)
    (hUb : U * LinearMap.toMatrix' (ρ permutationB) = Cb * N + bMatrix i * U)
    (hsurj : ∀ y : Vector i, ∃ x, N.mulVec x = 0 ∧ U.mulVec x = y) :
    Nonempty (MarkedAction i) := by
  let K := N.mulVecLin.ker
  have stable_generator (g : Carrier) (C : Matrix (Fin r) (Fin r) (ZMod 2))
      (h : N * LinearMap.toMatrix' (ρ g) = C * N) :
      ∀ x ∈ K, ρ g x ∈ K := by
    intro x hx
    change N.mulVec (ρ g x) = 0
    rw [← LinearMap.toMatrix'_mulVec, Matrix.mulVec_mulVec, h,
      ← Matrix.mulVec_mulVec]
    change N.mulVec x = 0 at hx
    rw [hx, Matrix.mulVec_zero]
  have hK : ∀ g, K ≤ K.comap (ρ g) :=
    invariant_of_generators ρ K (stable_generator _ _ hNa) (stable_generator _ _ hNb)
  let ρK := ρ.subrepresentation K hK
  let q : K →ₗ[ZMod 2] Vector i := U.mulVecLin.comp K.subtype
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx, hy⟩ := hsurj y
    exact ⟨⟨x, hx⟩, hy⟩
  have compatibility (g : Carrier) (C : Matrix (Fin (binaryDegree i)) (Fin r) (ZMod 2))
      (M : Mat i) (h : U * LinearMap.toMatrix' (ρ g) = C * N + M * U)
      (x : K) : q (ρK g x) = M.mulVecLin (q x) := by
    change U.mulVec (ρ g x.val) = M.mulVec (U.mulVec x.val)
    rw [← LinearMap.toMatrix'_mulVec, Matrix.mulVec_mulVec, h,
      Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hx : N.mulVec x.val = 0 := x.property
    rw [hx, Matrix.mulVec_zero, zero_add]
  obtain ⟨σ, _, ha, hb⟩ := exists_quotientAction_of_generators ρK q hq
    (aMatrix i).mulVecLin (bMatrix i).mulVecLin
    (compatibility _ _ _ hUa) (compatibility _ _ _ hUb)
  refine ⟨⟨σ, ?_, ?_⟩⟩
  · rw [ha]
    exact Matrix.toLin'.symm_apply_apply _
  · rw [hb]
    exact Matrix.toLin'.symm_apply_apply _

/-- The kernel-free case used for the invariant degree-1000 rows of
`exteriorSquare (56)`. The actual ambient action, marking and full row rank
remain the producer's obligations. -/
theorem markedAction_of_invariantRows (i : Fin 4) (m : ℕ)
    (ρ : Representation (ZMod 2) Carrier (Fin m → ZMod 2))
    (U : Matrix (Fin (binaryDegree i)) (Fin m) (ZMod 2))
    (ha : U * LinearMap.toMatrix' (ρ permutationA) = aMatrix i * U)
    (hb : U * LinearMap.toMatrix' (ρ permutationB) = bMatrix i * U)
    (hsurj : Function.Surjective U.mulVecLin) : Nonempty (MarkedAction i) := by
  have compatibility (g : Carrier) (M : Mat i)
      (h : U * LinearMap.toMatrix' (ρ g) = M * U) (x : Fin m → ZMod 2) :
      U.mulVecLin (ρ g x) = M.mulVecLin (U.mulVecLin x) := by
    change U.mulVec (ρ g x) = M.mulVec (U.mulVec x)
    rw [← LinearMap.toMatrix'_mulVec, Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
  obtain ⟨σ, _, hσa, hσb⟩ := exists_quotientAction_of_generators ρ U.mulVecLin hsurj
    (aMatrix i).mulVecLin (bMatrix i).mulVecLin
    (compatibility _ _ ha) (compatibility _ _ hb)
  refine ⟨⟨σ, ?_, ?_⟩⟩
  · rw [hσa]
    exact Matrix.toLin'.symm_apply_apply _
  · rw [hσb]
    exact Matrix.toLin'.symm_apply_apply _

end Representation.HigmanSims.LargeModels.Binary.Large.Descent
