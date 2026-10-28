module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Descent
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.LinearAlgebra.Trace

/-!
# Tensor normalizer rigidity on involution displacements

For the genuine coefficient-twisted tensor, the trace of an element with natural
trace t is t σ(t). A linear intertwiner implementing an inner-field automorphism
therefore restricts its field part to the identity or σ. Absolute irreducibility
over the actual Schur field identifies the remaining commutant with scalars.

The σ branch is scalar times an inner action followed by interchange of tensor
factors. An involution displacement contains u tensor W with u nonzero and W of
dimension at least two. Fixing this space after interchange would put W in a
line, a contradiction. Thus a diagram-preserving normalizer fixing the
involution displacement induces an inner automorphism.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

public section
set_option linter.unusedSimpArgs false
open Representation
open scoped TensorProduct
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment
variable {F : Type*} [Field F]

private theorem right_space_finrank_le_one
    (u z : Vector F) (hu : u ≠ 0) (W : Submodule F (Vector F))
    (h : ∀ y ∈ W, ∃ x : Vector F, x ⊗ₜ[F] z = u ⊗ₜ[F] y) :
    Module.finrank F W ≤ 1 := by
  have hex : ∃ i, u i ≠ 0 := by
    by_contra! hh
    exact hu (funext hh)
  obtain ⟨i, hi⟩ := hex
  have hle : W ≤ Submodule.span F {z} := by
    intro y hy
    obtain ⟨x, hx⟩ := h y hy
    have he := congrArg coordinates hx
    rw [coordinates_tmul, coordinates_tmul] at he
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x i / u i, ?_⟩
    ext k
    have hk := congrArg (fun X : Mat (F := F) => X i k) he
    change x i * z k = u i * y k at hk
    change (x i / u i) * z k = y k
    apply (mul_left_cancel₀ hi)
    calc
      u i * (x i / u i * z k) = x i * z k := by field_simp
      _ = u i * y k := hk
  exact (Submodule.finrank_mono hle).trans (by simpa using finrank_span_le_card ({z} : Set (Vector F)))

private theorem involution_kernel_large [CharP F 2] (a : Sp F) (ha : a ^ 2 = 1) :
    2 ≤ Module.finrank F (LinearMap.ker (symplecticNatural 2 a - LinearMap.id)) := by
  let d := symplecticNatural 2 a - (LinearMap.id : Module.End F (Vector F))
  have hle : LinearMap.range d ≤ LinearMap.ker d := by
    rintro _ ⟨v, rfl⟩
    change (symplecticNatural 2 a (symplecticNatural 2 a v - v) -
      (symplecticNatural 2 a v - v)) = 0
    have hh : symplecticNatural 2 a (symplecticNatural 2 a v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ha, map_one]
      rfl
    rw [map_sub, hh]
    ext i
    simp [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hb := Submodule.finrank_mono hle
  have hd := d.finrank_range_add_finrank_ker
  have hdim : Module.finrank F (Vector F) = 4 := by
    simp [Theory.SpecificGroups.SymplecticFour.Vector, Module.finrank_pi_fintype]
  rw [hdim] at hd
  change 2 ≤ Module.finrank F (LinearMap.ker d)
  omega

/-- Swapping the tensor factors, even with an arbitrary scalar and an inner
correction, cannot fix the displacement of a nonidentity natural involution. -/
theorem inner_swap_not_displacement_fixer [CharP F 2]
    (σ : F ≃+* F) (a j : Sp F) (hj : orderOf j = 2) (c : F) :
    ¬ ∀ z : Vector F ⊗[F] Vector F,
      c • twistedTensor σ a ((TensorProduct.comm F (Vector F) (Vector F))
        ((twistedTensor σ j - (LinearMap.id : Module.End F (Vector F ⊗[F] Vector F))) z)) =
          (twistedTensor σ j - (LinearMap.id : Module.End F (Vector F ⊗[F] Vector F))) z := by
  intro hfix
  have hjne : j ≠ 1 := by intro he; simp [he] at hj
  have hex : ∃ v, symplecticNatural 2 j v - v ≠ 0 := by
    by_contra! hh
    apply hjne
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext v
    change j.val.mulVec v = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec v
    rw [Matrix.one_mulVec]
    exact sub_eq_zero.mp (hh v)
  obtain ⟨v, hv⟩ := hex
  let u := symplecticNatural 2 j v - v
  let W := LinearMap.ker
    (symplecticNatural 2 (DiagramAutomorphisms.fieldAutomorphism σ j) - LinearMap.id)
  have hW : 2 ≤ Module.finrank F W := involution_kernel_large _ (by
    rw [← map_pow, (orderOf_eq_prime_iff.mp hj).1, map_one])
  have hsmall : Module.finrank F W ≤ 1 := by
    apply right_space_finrank_le_one u
      (symplecticNatural 2 (DiagramAutomorphisms.fieldAutomorphism σ a) u) hv W
    intro y hy
    have hy' : symplecticNatural 2 (DiagramAutomorphisms.fieldAutomorphism σ j) y = y :=
      sub_eq_zero.mp hy
    have hd : (twistedTensor σ j - (LinearMap.id : Module.End F (Vector F ⊗[F] Vector F))) (v ⊗ₜ[F] y) = u ⊗ₜ[F] y := by
      change symplecticNatural 2 j v ⊗ₜ[F]
        symplecticNatural 2 (DiagramAutomorphisms.fieldAutomorphism σ j) y - v ⊗ₜ[F] y = _
      rw [hy', ← TensorProduct.sub_tmul]
    have hh := hfix (v ⊗ₜ[F] y)
    rw [hd, TensorProduct.comm_tmul] at hh
    refine ⟨c • symplecticNatural 2 a y, ?_⟩
    change c • (symplecticNatural 2 a y ⊗ₜ[F]
      symplecticNatural 2 (DiagramAutomorphisms.fieldAutomorphism σ a) u) = _ at hh
    simpa only [TensorProduct.smul_tmul'] using hh
  omega
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment
public section
set_option linter.unusedSimpArgs false
open Representation
open scoped TensorProduct
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment
variable {F : Type*} [Field F]

private theorem eq_refl_or_sigma_of_norm (σ τ : F ≃+* F)
    (hN : ∀ z, τ z * σ (τ z) = z * σ z) :
    τ = RingEquiv.refl F ∨ τ = σ := by
  have htrace (z : F) : τ z + σ (τ z) = z + σ z := by
    have hh := hN (z + 1)
    simp only [map_add, map_one] at hh
    linear_combination hh - hN z
  have heither (z : F) : τ z = z ∨ τ z = σ z := by
    have hp : (τ z - z) * (τ z - σ z) = 0 := by
      linear_combination τ z * htrace z - hN z
    simpa only [mul_eq_zero, sub_eq_zero] using hp
  by_cases h : ∀ z, τ z = z
  · exact Or.inl (RingEquiv.ext h)
  · push Not at h
    obtain ⟨t, ht⟩ := h
    have htt := (heither t).resolve_left ht
    right
    apply RingEquiv.ext
    intro z
    rcases heither z with hz | hz
    · rcases heither (t + z) with htz | htz
      · rw [map_add, hz] at htz
        exact (ht (add_right_cancel htz)).elim
      · rw [map_add, htt, hz, map_add] at htz
        exact hz.trans (add_left_cancel htz)
    · exact hz

private theorem trace_natural (g : Sp F) :
    LinearMap.trace F (Vector F) (symplecticNatural 2 g) = Matrix.trace g.val := by
  exact Matrix.trace_toLin'_eq g.val

private theorem trace_twistedTensor (σ : F ≃+* F) (g : Sp F) :
    LinearMap.trace F (Vector F ⊗[F] Vector F) (twistedTensor σ g) =
      Matrix.trace g.val * σ (Matrix.trace g.val) := by
  rw [twistedTensor, Representation.tprod_apply, LinearMap.trace_tensorProduct',
    MonoidHom.comp_apply, trace_natural, trace_natural]
  change Matrix.trace g.val * Matrix.trace (g.val.map σ) = _
  rw [← AddMonoidHom.map_trace]

private theorem trace_inner_field (a x : Sp F) (τ : F ≃+* F) :
    Matrix.trace ((MulAut.conj a * fieldAutomorphism τ) x).val =
      τ (Matrix.trace x.val) := by
  have hc : a⁻¹.val * a.val = 1 := congrArg Subtype.val (inv_mul_cancel a)
  change Matrix.trace (a.val * (x.val.map τ) * a⁻¹.val) = _
  rw [Matrix.trace_mul_cycle, hc, Matrix.one_mul, ← AddMonoidHom.map_trace]

open Representation.OneCohomology.SymplecticFour in
private theorem exists_trace [CharP F 2] (t : F) : ∃ x : Sp F, Matrix.trace x.val = t := by
  refine ⟨rootElement 0 t * rootElement 1 1, ?_⟩
  simp [rootElement, rootMatrix, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
    Matrix.one_apply, CharTwo.add_self_eq_zero, add_assoc, add_comm, add_left_comm]

/-- The tensor character restricts a linearly implemented field automorphism
 to the identity or the quadratic coefficient involution. -/
theorem tensor_intertwiner_field_alternatives [CharP F 2]
    (σ τ : F ≃+* F) (a : Sp F)
    (U : (Vector F ⊗[F] Vector F) ≃ₗ[F] (Vector F ⊗[F] Vector F))
    (hi : ∀ (x : Sp F) z, U (twistedTensor σ x z) =
      twistedTensor σ ((MulAut.conj a * fieldAutomorphism τ) x) (U z)) :
    τ = RingEquiv.refl F ∨ τ = σ := by
  apply eq_refl_or_sigma_of_norm σ τ
  intro t
  obtain ⟨x, hx⟩ := exists_trace t
  have he : U.conj (twistedTensor σ x) =
      twistedTensor σ ((MulAut.conj a * fieldAutomorphism τ) x) := by
    apply LinearMap.ext
    intro z
    change U (twistedTensor σ x (U.symm z)) = _
    rw [hi, LinearEquiv.apply_symm_apply]
  have ht := LinearMap.trace_conj' (twistedTensor σ x) U
  rw [he, trace_twistedTensor, trace_twistedTensor, trace_inner_field, hx] at ht
  exact ht
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {D V F : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [IsIrreducible ρ] [Field F] [Algebra (SchurField ρ) F]

/-- The full tensor commutant is scalar, by absolute irreducibility over the
actual Schur field and the specified scalar-extension intertwiner. -/
theorem tensor_commutant_scalar {s : ℕ} (h : TensorIdentification ρ F s)
    (f : Module.End F (Vector F ⊗[F] Vector F))
    (hf : ∀ x z, f (twistedTensor h.sigma.toRingEquiv x z) =
      twistedTensor h.sigma.toRingEquiv x (f z)) :
    ∃ c : F, ∀ z, f z = c • z := by
  let : Module.Finite (SchurField ρ) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) (SchurField ρ) ρ.asModule
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let τ := extendScalars F ρ.endFieldRep
  let : IsIrreducible τ := IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep F
  have hab : IsAbsolutelyIrreducible τ :=
    (IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_extendScalars ρ.endFieldRep F).mpr
      (endFieldRep_isAbsolutelyIrreducible ρ)
  let f' : Representation.End τ :=
    { toLinearMap := h.linearEquiv.symm.toLinearMap.comp (f.comp h.linearEquiv.toLinearMap)
      isIntertwining' := by
        intro x
        apply LinearMap.ext
        intro v
        apply h.linearEquiv.injective
        change h.linearEquiv (h.linearEquiv.symm (f (h.linearEquiv (τ x v)))) =
          h.linearEquiv (τ x (h.linearEquiv.symm (f (h.linearEquiv v))))
        simp only [τ, LinearEquiv.apply_symm_apply, h.intertwines, hf] }
  obtain ⟨c, hc⟩ := (isAbsolutelyIrreducible_iff_surjective τ).mp hab f'
  refine ⟨c, ?_⟩
  intro z
  have he := congrArg (fun q : Representation.End τ => q (h.linearEquiv.symm z)) hc
  change c • h.linearEquiv.symm z = h.linearEquiv.symm (f (h.linearEquiv (h.linearEquiv.symm z))) at he
  have hh := congrArg h.linearEquiv he
  simpa using hh.symm
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F]

private theorem field_twice (σ : F ≃+* F) (hσ : Function.Involutive σ) (x : Sp F) :
    fieldAutomorphism σ (fieldAutomorphism σ x) = x := by
  apply Subtype.ext
  ext i j
  exact hσ (x.val i j)

/-- The factor interchange implements the coefficient involution on the genuine tensor. -/
theorem swap_intertwines (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (x : Sp F) (z : Vector F ⊗[F] Vector F) :
    TensorProduct.comm F (Vector F) (Vector F) (twistedTensor σ x z) =
      twistedTensor σ (fieldAutomorphism σ x)
        (TensorProduct.comm F (Vector F) (Vector F) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul v w =>
    change symplecticNatural 2 (fieldAutomorphism σ x) w ⊗ₜ[F] symplecticNatural 2 x v =
      symplecticNatural 2 (fieldAutomorphism σ x) w ⊗ₜ[F]
        symplecticNatural 2 (fieldAutomorphism σ (fieldAutomorphism σ x)) v
    rw [field_twice σ hσ]

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [IsIrreducible ρ] [Algebra (SchurField ρ) F] [CharP F 2] [Finite F]

/-- A diagram-preserving tensor normalizer fixing an involution displacement
induces an inner automorphism. All operators act on the actual coefficient-twisted tensor. -/
theorem tensor_fixer_inner {s : ℕ} (h : TensorIdentification ρ F s)
    (α : MulAut (Sp F)) (hα : PreservesDiagram α)
    (U : (Vector F ⊗[F] Vector F) ≃ₗ[F] (Vector F ⊗[F] Vector F))
    (hi : ∀ x z, U (twistedTensor h.sigma.toRingEquiv x z) =
      twistedTensor h.sigma.toRingEquiv (α x) (U z))
    (j : Sp F) (hj : orderOf j = 2)
    (hfix : ∀ z, U (twistedTensor h.sigma.toRingEquiv j z - z) =
      twistedTensor h.sigma.toRingEquiv j z - z) :
    α ∈ MulAut.innerSubgroup (Sp F) := by
  obtain ⟨a, τ, ha⟩ := SemilinearClassification.inner_field_of_preservesDiagram α hα
  have hi' : ∀ x z, U (twistedTensor h.sigma.toRingEquiv x z) =
      twistedTensor h.sigma.toRingEquiv ((MulAut.conj a * fieldAutomorphism τ) x) (U z) := by
    simpa only [ha] using hi
  rcases tensor_intertwiner_field_alternatives h.sigma.toRingEquiv τ a U hi' with hτ | hτ
  · have he : fieldAutomorphism (RingEquiv.refl F) = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rfl
    rw [hτ, he, mul_one] at ha
    exact ⟨a, ha.symm⟩
  · rw [hτ] at hi'
    let R := twistedTensor h.sigma.toRingEquiv
    let S := TensorProduct.comm F (Vector F) (Vector F)
    let f : Module.End F (Vector F ⊗[F] Vector F) :=
      S.toLinearMap.comp ((R a⁻¹).comp U.toLinearMap)
    have hf : ∀ x z, f (R x z) = R x (f z) := by
      intro x z
      change S (R a⁻¹ (U (R x z))) = R x (S (R a⁻¹ (U z)))
      rw [hi']
      have hm : R a⁻¹ (R ((MulAut.conj a * fieldAutomorphism h.sigma.toRingEquiv) x) (U z)) =
          R (fieldAutomorphism h.sigma.toRingEquiv x) (R a⁻¹ (U z)) := by
        change R a⁻¹ (R (a * fieldAutomorphism h.sigma.toRingEquiv x * a⁻¹) (U z)) = _
        simp only [map_mul, Module.End.mul_apply]
        simp
      rw [hm, swap_intertwines h.sigma.toRingEquiv h.sigma_involutive, field_twice _ h.sigma_involutive]
    obtain ⟨c, hc⟩ := tensor_commutant_scalar ρ h f hf
    have hU (z) : U z = c • R a (S z) := by
      have he := congrArg (fun w => R a (S w)) (hc z)
      change R a (S (S (R a⁻¹ (U z)))) = R a (S (c • z)) at he
      simpa [S, TensorProduct.comm_symm] using he
    exfalso
    apply inner_swap_not_displacement_fixer h.sigma.toRingEquiv a j hj c
    intro z
    rw [← hU]
    exact hfix z
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment
