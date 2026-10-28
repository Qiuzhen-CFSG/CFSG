module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Displacement bounds from a filtration and two factors

A linear map has image dimension at most the codimension of a subspace plus
its image dimension on that subspace. Taking a complement proves the estimate;
a surjective intertwiner then carries it to the actual quotient action.
Conversely, a specified decomposition into two invariant factors embeds the
product of their images in the original image.

These are the linear-algebra ingredients of the last contradiction in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), proof of Theorem 12.6.34, printed p.838 (PDF p.855).
-/

public section
open Module

namespace LinearMap
variable {k U W Q : Type*} [Field k]
  [AddCommGroup U] [Module k U] [FiniteDimensional k U]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]

omit [FiniteDimensional k W] in
/-- The image of a linear map is bounded by its image on a subspace plus
the codimension of that subspace. No invariance of the subspace is needed. -/
theorem finrank_range_le_quotient_add_map (f : U →ₗ[k] W) (D : Submodule k U) :
    finrank k f.range ≤ finrank k (U ⧸ D) + finrank k (D.map f) := by
  obtain ⟨E, hE⟩ := D.exists_isCompl
  have heq : f.range = D.map f ⊔ E.map f := by
    rw [← Submodule.map_sup, hE.sup_eq_top, Submodule.map_top]
  have he := Submodule.finrank_add_eq_of_isCompl hE
  have hd := D.finrank_quotient_add_finrank
  have hm := Submodule.finrank_map_le f E
  have hs := Submodule.finrank_add_le_finrank_add_finrank (D.map f) (E.map f)
  rw [heq]
  omega

omit [FiniteDimensional k Q] in
/-- A surjective intertwiner transfers the filtration bound to the target.
The image of `D` under `f` need only lie in `A`; `D` need not be invariant. -/
theorem finrank_range_le_of_surjective_intertwining (f : U →ₗ[k] U) (g : Q →ₗ[k] Q)
    (q : U →ₗ[k] Q) (hq : Function.Surjective q)
    (he : ∀ u, q (f u) = g (q u)) (D A : Submodule k U)
    (hDA : ∀ u ∈ D, f u ∈ A) :
    finrank k g.range ≤ finrank k (U ⧸ D) + finrank k A := by
  have hc : q.comp f = g.comp q := LinearMap.ext he
  have hr : (q.comp f).range = g.range := by
    rw [hc, LinearMap.range_comp_of_range_eq_top g (LinearMap.range_eq_top.mpr hq)]
  have hmap : D.map (q.comp f) ≤ A.map q := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨f u, hDA u hu, rfl⟩
  have hb := finrank_range_le_quotient_add_map (q.comp f) D
  rw [hr] at hb
  exact hb.trans (Nat.add_le_add_left
    ((Submodule.finrank_mono hmap).trans (Submodule.finrank_map_le q A)) _)

/-- Two diagonal factors inject their displacement images independently into
the image of the original map, through the specified linear equivalence. -/
theorem finrank_range_add_le_of_intertwining_prod (f : U →ₗ[k] U) (s : W →ₗ[k] W) (t : Q →ₗ[k] Q)
    (e : U ≃ₗ[k] W × Q) (he : ∀ u, e (f u) = (s (e u).1, t (e u).2)) :
    finrank k s.range + finrank k t.range ≤ finrank k f.range := by
  let j : (s.range × t.range) →ₗ[k] f.range :=
    (e.symm.toLinearMap.comp (s.range.subtype.prodMap t.range.subtype)).codRestrict
      f.range (by
        rintro ⟨⟨x, x0, rfl⟩, ⟨y, y0, rfl⟩⟩
        refine ⟨e.symm (x0, y0), ?_⟩
        apply e.injective
        simpa using he (e.symm (x0, y0)))
  have hj : Function.Injective j := by
    intro x y h
    have hv := congrArg (fun z : f.range => e z.val) h
    have hv' : (x.1.val, x.2.val) = (y.1.val, y.2.val) := by
      simpa [j] using hv
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hv'))
      (Subtype.ext (congrArg Prod.snd hv'))
  simpa only [Module.finrank_prod] using LinearMap.finrank_le_finrank_of_injective hj
end LinearMap

end
