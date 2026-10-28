module

public import Theory.SpecificGroups.SL3.PRegularClasses.TraceParameters
public import Theory.Representation.ScalarDescent
public import Theory.AlgebraicGroup.Representations.Semisimple
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# General-linear intertwiners for odd-order special linear matrices

Two odd-order elements of SL₃ in characteristic two with the same characteristic
polynomial admit an invertible intertwiner over the original field. Over an
algebraic closure, the separable annihilator `Xⁿ - 1` supplies eigenbases. The
multiset of roots of the characteristic polynomial matches these bases, including
all repeated eigenvalues and the entire eigenvalue-one space. The resulting
isomorphism of representations of the infinite cyclic group descends by the
proved Noether–Deuring theorem `Representation.repEquiv_of_extendScalars`.

This is the general-linear input to the odd-order special linear conjugacy argument
used in the SL₃ module catalogue. The eigenbasis and scalar-descent proof is
adapted from `SymplecticFour/PRegularClasses/GLIntertwiner.lean`.
Source context: GLS III, 2.8.2 and 2.8.6(a), `refs/KGroup/GLS3/chapter2.tex`.
-/

namespace Theory.SpecificGroups.SL3.PRegularClasses

open Polynomial

private theorem eigenbasis_charpoly {K V I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype I] [DecidableEq I] (f : Module.End K V)
    (b : Module.Basis I K V) (μ : I → K) (hb : ∀ i, f (b i) = μ i • b i) :
    f.charpoly = ∏ i, (X - C (μ i)) := by
  rw [← LinearMap.charpoly_toMatrix f b]
  have hd : LinearMap.toMatrix b b f = Matrix.diagonal μ := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [LinearMap.toMatrix_apply, hb]
    · simp [LinearMap.toMatrix_apply, hb, Matrix.diagonal, hij]
  rw [hd, Matrix.charpoly_diagonal]

private theorem roots_eigenvalues {K A : Type*} [Field K] [Fintype A] (a : A → K) :
    (∏ i, (X - C (a i))).roots = Finset.univ.val.map a := by
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod] using
    roots_multiset_prod_X_sub_C (Finset.univ.val.map a)

private theorem eigenvalues_equiv_of_prod_eq {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    (μ : I → K) (ν : J → K)
    (h : (∏ i, (X - C (μ i))) = ∏ j, (X - C (ν j))) :
    ∃ e : I ≃ J, ∀ i, ν (e i) = μ i := by
  classical
  have hm := congrArg Polynomial.roots h
  rw [roots_eigenvalues μ, roots_eigenvalues ν] at hm
  have hc (a : K) : Fintype.card {i // μ i = a} = Fintype.card {j // ν j = a} := by
    have hh := congrArg (Multiset.count a) hm
    simpa [Multiset.count_map, Fintype.card_subtype, ← Finset.filter_val, eq_comm] using hh
  let e := fun a => Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

private theorem exists_equiv_of_semisimple_charpoly_eq {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f g : Module.End K V) (hf : f.IsSemisimple) (hg : g.IsSemisimple)
    (hp : f.charpoly = g.charpoly) :
    ∃ e : V ≃ₗ[K] V, e.toLinearMap.comp f = g.comp e.toLinearMap := by
  classical
  obtain ⟨b, μ, hb⟩ :=
    Theory.AlgebraicGroup.Module.End.IsSemisimple.exists_fin_eigenbasis f hf
  obtain ⟨c, ν, hc⟩ :=
    Theory.AlgebraicGroup.Module.End.IsSemisimple.exists_fin_eigenbasis g hg
  rw [eigenbasis_charpoly f b μ hb, eigenbasis_charpoly g c ν hc] at hp
  obtain ⟨s, hs⟩ := eigenvalues_equiv_of_prod_eq μ ν hp
  refine ⟨b.equiv c s, ?_⟩
  apply b.ext
  intro i
  simp [LinearMap.comp_apply, hb, Module.Basis.equiv_apply, hc, hs]

private theorem repEquiv_of_generator_intertwiner {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    (ρ σ : Representation K (Multiplicative ℤ) V)
    (e : V ≃ₗ[K] V)
    (he : e.toLinearMap.comp (ρ (Multiplicative.ofAdd 1)) =
      (σ (Multiplicative.ofAdd 1)).comp e.toLinearMap) :
    Nonempty (ρ ≃ₗ σ) := by
  have hconj : e.conjRingEquiv.toMonoidHom.comp ρ = σ := by
    apply MonoidHom.ext_mint
    ext x
    have hx := LinearMap.congr_fun he (e.symm x)
    simpa using hx
  refine ⟨Representation.RepEquiv.mk e ?_⟩
  intro n
  ext x
  have hx := LinearMap.congr_fun (DFunLike.congr_fun hconj n) (e x)
  simpa using hx

variable {F : Type*} [Field F]

private def naturalRep : Representation F (Matrix.SpecialLinearGroup (Fin 3) F)
    (Fin 3 → F) where
  toFun g := Matrix.toLin' g.val
  map_one' := by simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]
    rfl

private def cyclicRep (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    Representation F (Multiplicative ℤ) (Fin 3 → F) :=
  naturalRep.comp (zpowersHom _ g)

private theorem cyclicRep_generator (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    cyclicRep g (Multiplicative.ofAdd 1) = Matrix.toLin' g.val := by
  simp [cyclicRep, naturalRep]

private theorem cyclicRep_generator_pow (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    cyclicRep g (Multiplicative.ofAdd 1) ^ orderOf g = 1 := by
  change naturalRep (g ^ (1 : ℤ)) ^ orderOf g = 1
  rw [zpow_one, ← map_pow, pow_orderOf_eq_one, map_one]

private theorem cyclicRep_semisimple [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 3) F) (hg : ¬ 2 ∣ orderOf g) :
    Module.End.IsSemisimple
      ((cyclicRep g (Multiplicative.ofAdd 1)).baseChange (AlgebraicClosure F)) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C' 2 (orderOf g) (1 : AlgebraicClosure F) hg one_ne_zero).squarefree
  simp only [map_sub, Polynomial.aeval_X_pow, map_one]
  rw [← LinearMap.baseChange_pow, cyclicRep_generator_pow, LinearMap.baseChange_one, sub_self]

/-- Equal characteristic polynomials of odd-order special linear matrices give a
unit intertwiner over the original field. No finiteness or field-size assumption
is needed, and repeated characteristic-polynomial factors are allowed. -/
public theorem exists_unit_intertwiner_of_charpoly_eq [CharP F 2] (g h : Matrix.SpecialLinearGroup (Fin 3) F)
    (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (hpoly : g.val.charpoly = h.val.charpoly) :
    ∃ D : Matrix (Fin 3) (Fin 3) F,
      IsUnit D ∧ D * g.val = h.val * D := by
  have hp' : ((cyclicRep g (Multiplicative.ofAdd 1)).baseChange (AlgebraicClosure F)).charpoly =
      ((cyclicRep h (Multiplicative.ofAdd 1)).baseChange (AlgebraicClosure F)).charpoly := by
    simp only [LinearMap.charpoly_baseChange, cyclicRep_generator, Matrix.charpoly_toLin', hpoly]
  obtain ⟨e, he⟩ := exists_equiv_of_semisimple_charpoly_eq _ _ (cyclicRep_semisimple g hg)
    (cyclicRep_semisimple h hh) hp'
  obtain ⟨d⟩ := Representation.repEquiv_of_extendScalars (cyclicRep g) (cyclicRep h)
    (repEquiv_of_generator_intertwiner (Representation.extendScalars (AlgebraicClosure F) (cyclicRep g))
      (Representation.extendScalars (AlgebraicClosure F) (cyclicRep h)) e he)
  refine ⟨LinearMap.toMatrix' d.toLinearMap, ?_, ?_⟩
  · rw [LinearMap.isUnit_toMatrix'_iff, Module.End.isUnit_iff]
    exact d.toLinearEquiv.bijective
  · have hd := congrArg LinearMap.toMatrix' (d.isIntertwining' (Multiplicative.ofAdd 1))
    simpa only [LinearMap.toMatrix'_comp, cyclicRep_generator, LinearMap.toMatrix'_toLin'] using hd

end Theory.SpecificGroups.SL3.PRegularClasses
