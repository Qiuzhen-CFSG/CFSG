module

public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.Representation.HigmanRelativeTrace

/-!
# Projectivity of the binary natural module for A₅

On the augmentation kernel of the five-coordinate permutation module, take
`a(v) = v(0) • (e₀ + e₁)`. Its conjugate sum over `A₅` is the identity.
Indeed, each ordered pair of distinct coordinates occurs three times. In
characteristic two the full-space trace matrix therefore has zero diagonal
and all off-diagonal entries equal to one. It sends `v` to
`v + (∑ i, v i) • allOne`, and hence fixes the augmentation kernel.

We check the 25 matrix coefficients in Lean's kernel, apply Higman's relative-trace
criterion, and transfer projectivity along the odd-degree equivariant
identification of the core with the natural deleted-permutation module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(1), printed p.408 (PDF p.419), citing
Exercise 6.3 of Aschbacher, *Finite Group Theory* (1986). The natural module is
the orthogonal/deleted-permutation module of §B.3.
-/

public section

open scoped BigOperators

namespace BinaryPermutation

set_option maxRecDepth 10000 in
private theorem alternatingFive_trace_coefficients : ∀ i j : Fin 5,
    (∑ g : alternatingGroup (Fin 5),
      (if g.val.symm 0 = j then (if g.val i = 0 then 1 else 0) +
        (if g.val i = 1 then 1 else 0) else 0 : ZMod 2)) =
      (if i = j then 0 else 1) := by
  decide +kernel

private def traceSeed : core (Fin 5) →ₗ[ZMod 2] core (Fin 5) where
  toFun v := ⟨fun i => v.val 0 * ((if i = 0 then 1 else 0) + (if i = 1 then 1 else 0)), by
    simp [mem_core, Fin.sum_univ_succ]
    exact CharTwo.add_self_eq_zero _⟩
  map_add' v w := by ext i; exact add_mul _ _ _
  map_smul' c v := by ext i; exact mul_assoc _ _ _

private theorem traceSeed_sum (v : core (Fin 5)) :
    ∑ g : alternatingGroup (Fin 5), alternatingCoreRepresentation (Fin 5) g⁻¹
      (traceSeed (alternatingCoreRepresentation (Fin 5) g v)) = v := by
  apply Subtype.ext
  funext i
  simp only [Submodule.coe_sum, Finset.sum_apply]
  change (∑ g : alternatingGroup (Fin 5), v.val (g.val.symm 0) *
    ((if g.val i = 0 then 1 else 0) + (if g.val i = 1 then 1 else 0))) = v.val i
  calc
    _ = ∑ g : alternatingGroup (Fin 5), ∑ j : Fin 5, v.val j *
        (if g.val.symm 0 = j then (if g.val i = 0 then 1 else 0) +
          (if g.val i = 1 then 1 else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro g _
      simp
    _ = ∑ j : Fin 5, v.val j * (if i = j then 0 else 1) := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, alternatingFive_trace_coefficients]
    _ = v.val i := by
      have hv := v.property
      rw [mem_core] at hv
      have hsplit : (∑ j : Fin 5, v.val j * (if i = j then 0 else 1)) + v.val i = 0 := by
        calc
          _ = ∑ j : Fin 5, (v.val j * (if i = j then 0 else 1) +
              (if i = j then v.val j else 0)) := by
            rw [Finset.sum_add_distrib]
            simp
          _ = ∑ j : Fin 5, v.val j := by
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp
          _ = 0 := hv
      exact (eq_neg_iff_add_eq_zero.mpr hsplit).trans (CharTwo.neg_eq _)

/-- The augmentation kernel for `A₅` is projective over the binary group algebra. -/
theorem alternatingFive_core_projective :
    Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
      (alternatingCoreRepresentation (Fin 5)).asModule := by
  let ρ := alternatingCoreRepresentation (Fin 5)
  let a := ρ.asModuleEquiv.symm.conj traceSeed
  apply ModularBlock.HigmanRelativeTrace.projective_of_relative_trace_id a
  apply LinearMap.ext
  intro v
  apply ρ.asModuleEquiv.injective
  simp only [LinearMap.sum_apply, LinearMap.id_apply, map_sum,
    LinearMap.conjugate_apply, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul]
  simp only [a, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul]
  exact traceSeed_sum _

/-- The projectivity assertion of Aschbacher–Smith I.1.6(1): the four-dimensional
natural deleted-permutation module for `A₅` is projective. -/
theorem alternatingFive_natural_projective :
    Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
      (alternatingNaturalRepresentation (Fin 5)).asModule := by
  let := alternatingFive_core_projective
  let e := coreEquivNatural (Fin 5) (by decide)
  let f : (alternatingCoreRepresentation (Fin 5)).IntertwiningMap
      (alternatingNaturalRepresentation (Fin 5)) :=
    { toLinearMap := e.toLinearMap
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro v
        exact coreEquivNatural_equivariant (Fin 5) (by decide) g.val v }
  let F := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  let E := LinearEquiv.ofBijective F e.bijective
  exact Module.Projective.of_equiv E

end BinaryPermutation
