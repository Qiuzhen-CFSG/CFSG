module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_4
public import Theory.AlgebraicGroup.Cartan.Kernels
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
The type `E₇` universal-center core.  The Cartan equations for the seven
fundamental coroot coordinates have a common kernel with one parameter of
order two, supported in coordinates `3`, `4`, and `6`.  This module records
that calculation as a multiplicative-group equivalence and isolates the
remaining geometric input: an identification of the ambient center with
this Cartan kernel.  The latter is supplied by the center/weight-lattice
bridge proved from the GLS3 Theorem 1.12.5(c) hypotheses.

The explicit kernel calculation uses the integral left inverse of the `E₇`
Cartan matrix from `Theory.AlgebraicGroup.Cartan.Kernels`, followed by the
coordinate reduction in `dynkinCartanRelationKernel_E7`.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators

universe u

variable {k : Type u} [Field k]

/-- The common multiplicative kernel of the standard type-`E₇` Cartan
relations on seven coordinate units. -/
@[expose]
public def e7CartanRelationKernel : Subgroup (Fin 7 → kˣ) where
  carrier := {t : Fin 7 → kˣ | ∀ j : Fin 7,
    (∏ i : Fin 7, t i ^ dynkinCartanEntry ⟨.E7, 7⟩ i j) = 1}
  one_mem' := by
    intro j
    simp
  mul_mem' := by
    intro a b ha hb j
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp_rw [Pi.mul_apply, mul_zpow]
    rw [Finset.prod_mul_distrib]
    rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha j
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp_rw [Pi.inv_apply, inv_zpow]
    rw [Finset.prod_inv_distrib]
    rw [ha]
    simp

/-- The order-two parameter inserted in the three nontrivial `E₇`
coordinates. -/
@[expose]
public def e7CartanRelationKernelMap : _root_.rootsOfUnity 2 k →*
    e7CartanRelationKernel (k := k) := by
  let f : _root_.rootsOfUnity 2 k →* (Fin 7 → kˣ) :=
    { toFun := fun ω i => if i.val = 3 ∨ i.val = 4 ∨ i.val = 6 then ω else 1
      map_one' := by
        ext ω
        simp
      map_mul' := by
        intro ω ζ
        funext i
        by_cases hi : i.val = 3 ∨ i.val = 4 ∨ i.val = 6 <;> simp [hi] }
  exact f.codRestrict e7CartanRelationKernel (by
    intro ω
    have hω : (ω : kˣ) ^ (2 : ℕ) = 1 :=
      (mem_rootsOfUnity 2 (ω : kˣ)).mp ω.property
    have hωinv : (ω : kˣ)⁻¹ ^ (2 : ℕ) = 1 := by
      rw [inv_pow, hω, inv_one]
    have hωinv_mul : (ω : kˣ)⁻¹ * (ω : kˣ)⁻¹ = 1 := by
      simpa [pow_two] using hωinv
    intro j
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk]
    fin_cases j <;>
      simp [dynkinCartanEntry, Fin.prod_univ_succ, hω, hωinv_mul])

@[simp]
public lemma e7CartanRelationKernelMap_apply
    (ω : _root_.rootsOfUnity 2 k) (i : Fin 7) :
    (e7CartanRelationKernelMap ω).1 i =
      if i.val = 3 ∨ i.val = 4 ∨ i.val = 6 then (ω : kˣ) else 1 := by
  change (if i.val = 3 ∨ i.val = 4 ∨ i.val = 6 then (ω : kˣ) else 1) = _
  rfl

public lemma e7CartanRelationKernelMap_injective :
    Function.Injective (e7CartanRelationKernelMap (k := k)) := by
  intro ω ζ h
  have h3 := congrArg (fun t => t.1 (3 : Fin 7)) h
  simpa [e7CartanRelationKernelMap_apply] using h3

public lemma e7CartanRelationKernelMap_surjective :
    Function.Surjective (e7CartanRelationKernelMap (k := k)) := by
  intro t
  rcases dynkinCartanRelationKernel_E7 t.1 t.2 with ⟨ω, hω, ht⟩
  let ω' : _root_.rootsOfUnity 2 k :=
    ⟨ω, by simpa [mem_rootsOfUnity] using hω⟩
  refine ⟨ω', ?_⟩
  apply Subtype.ext
  funext i
  rw [e7CartanRelationKernelMap_apply, ht]

/-- The explicit identification of the `E₇` Cartan kernel with the second
roots of unity. -/
public noncomputable def e7CartanRelationKernelEquiv :
    _root_.rootsOfUnity 2 k ≃* e7CartanRelationKernel (k := k) :=
  MulEquiv.ofBijective e7CartanRelationKernelMap
    ⟨e7CartanRelationKernelMap_injective, e7CartanRelationKernelMap_surjective⟩

/-- Convert a center/kernel identification into the `E₇` universal center
shape.  The hypothesis is the geometric center-to-Cartan-kernel bridge; the
present module supplies the complete `E₇` lattice calculation. -/
public theorem e7_hasCenterShape_of_centerRelationKernelEquiv
    {K : Variety k} [AlgebraicGroup K]
    (hCenter : Nonempty
      (Subgroup.center (Variety.Point K) ≃* e7CartanRelationKernel (k := k))) :
    HasCenterShape (K := K) (.rootsOfUnity 2) := by
  apply (hasCenterShape_rootsOfUnity_iff (K := K) 2).2
  exact Nonempty.map
    (fun e => e.trans (e7CartanRelationKernelEquiv (k := k)).symm) hCenter

/-- The universal, semisimple simple `E₇` specialization of the preceding
core.  `hCenter` is intentionally explicit: it is the source-faithful
center/weight-lattice identification and is not reconstructed from any
placeholder-backed theorem. -/
public theorem typeE7_universal_center_shape_core
    {K : Variety k} [AlgebraicGroup K]
    (_hK : IsSemisimpleAlgebraicGroup K)
    (_hSimple : IsSimpleAlgebraicGroup K)
    (_hType : HasRootSystemType K ⟨.E7, 7⟩)
    (_hUniversal : IsUniversalVersion K)
    (hCenter : Nonempty
      (Subgroup.center (Variety.Point K) ≃* e7CartanRelationKernel (k := k))) :
    HasCenterShape (K := K) (.rootsOfUnity 2) := by
  exact e7_hasCenterShape_of_centerRelationKernelEquiv hCenter

end Theory.AlgebraicGroup
