module

public import Theory.Representation.KrullSchmidt
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Projection

/-!
# Identifying nonprojective indecomposable summands

Given an isomorphism `U × A ≃ V × B`, with `U` and `V` indecomposable,
`U` nonprojective and `B` projective, the two composites through `V` and
`B` sum to the identity of `U`. Its local endomorphism ring makes one
composite invertible. The projective alternative is impossible; the other
splits `U` off `V`, and indecomposability gives `U ≃ V`.

This is the Krull--Schmidt uniqueness argument for the nonprojective part
of a Green restriction, used in Feit VII.1.4--5 and VII.2.25. The actual
subgroup-restriction consumer is in the sibling `NormalizerLength` module.
-/

public section
noncomputable section

namespace Module

private theorem equiv_of_split_of_indecomposable
    {R U V : Type*} [Ring R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] [Nontrivial U]
    (hV : IsIndecomposable R V)
    (i : U →ₗ[R] V) (q : V →ₗ[R] U) (hqi : q.comp i = LinearMap.id) :
    Nonempty (U ≃ₗ[R] V) := by
  have hqi' (u : U) : q (i u) = u := DFunLike.congr_fun hqi u
  have hi : Function.Injective i := Function.HasLeftInverse.injective ⟨q, hqi'⟩
  let f : V →ₗ[R] LinearMap.range i := i.rangeRestrict.comp q
  have hf (x : LinearMap.range i) : f x = x := by
    obtain ⟨u, hu⟩ := x.property
    apply Subtype.ext
    change i (q x) = x
    rw [← hu, hqi']
  have hc := LinearMap.isCompl_of_proj hf
  rcases hV.2 _ _ hc with hr | hk
  · have hz : i = 0 := LinearMap.range_eq_bot.mp hr
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    exact False.elim (hu (hi (by simp [hz])))
  · have hr : LinearMap.range i = ⊤ := by
      simpa [hk] using hc.sup_eq_top
    exact ⟨LinearEquiv.ofBijective i ⟨hi, LinearMap.range_eq_top.mp hr⟩⟩

/-- An indecomposable nonprojective summand cannot be lost in a projective
complement. This is the uniqueness argument needed for Green summands. -/
theorem nonprojective_indecomposable_equiv_of_prod_equiv
    {F R U V A B : Type*} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup U] [Module F U] [Module R U] [IsScalarTower F R U]
    [FiniteDimensional F U]
    [AddCommGroup V] [Module R V]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Projective R B]
    (hU : IsIndecomposable R U) (hV : IsIndecomposable R V)
    (hUnp : ¬ Projective R U) (e : (U × A) ≃ₗ[R] (V × B)) :
    Nonempty (U ≃ₗ[R] V) := by
  let : Nontrivial U := hU.1
  let : IsLocalRing (Module.End R U) :=
    end_isLocalRing_of_isIndecomposable (F := F) hU
  let : IsDedekindFiniteMonoid (Module.End R U) :=
    end_isDedekindFiniteMonoid (F := F)
  let f : U →ₗ[R] V := (LinearMap.fst R V B).comp
    (e.toLinearMap.comp (LinearMap.inl R U A))
  let a : U →ₗ[R] B := (LinearMap.snd R V B).comp
    (e.toLinearMap.comp (LinearMap.inl R U A))
  let g : V →ₗ[R] U := (LinearMap.fst R U A).comp
    (e.symm.toLinearMap.comp (LinearMap.inl R V B))
  let b : B →ₗ[R] U := (LinearMap.fst R U A).comp
    (e.symm.toLinearMap.comp (LinearMap.inr R V B))
  have hsum : g.comp f + b.comp a = (1 : Module.End R U) := by
    ext u
    change (e.symm (f u, 0)).1 + (e.symm (0, a u)).1 = u
    rw [← Prod.fst_add, ← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    change (e.symm (e (u, 0))).1 = u
    rw [e.symm_apply_apply]
  rcases isUnit_or_isUnit_of_isUnit_add (hsum ▸ isUnit_one) with hgf | hba
  · let c : U ≃ₗ[R] U :=
      LinearEquiv.ofBijective (g.comp f) ((Module.End.isUnit_iff _).mp hgf)
    apply equiv_of_split_of_indecomposable hV f (c.symm.toLinearMap.comp g)
    ext u
    exact c.symm_apply_apply u
  · let c : U ≃ₗ[R] U :=
      LinearEquiv.ofBijective (b.comp a) ((Module.End.isUnit_iff _).mp hba)
    apply False.elim
    apply hUnp
    apply Projective.of_split a (c.symm.toLinearMap.comp b)
    ext u
    exact c.symm_apply_apply u

end Module
