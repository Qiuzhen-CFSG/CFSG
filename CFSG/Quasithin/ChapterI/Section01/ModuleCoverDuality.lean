module

public import Theory.Representation.FirstCohomologyDuality

/-!
# I.1.5: Universal covers of modules

For a finite group and a finite-dimensional module `V = [V,G]`, the dual of
`U(G,V*)` is a cover of `V`. Every finite-dimensional cover is its equivariant
quotient, compatibly with the maps to `V`, and the central kernel dimension is
`dim H¹(G,V*)`. These statements apply over F₂ and, more generally, any field.

The proof dualizes the displacement-cocycle embedding. The dimension calculation
identifies the central kernel with the annihilator of the principal cocycles.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Remark I.1.5, printed p.408 (PDF p.419).
-/

public section
namespace CFSG.Quasithin.ChapterI

open Representation Representation.OneCohomology

variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W]

/-- The universal covering and its central-kernel dimension in Remark I.1.5. -/
theorem universalCover_and_kernel_dimension [Finite G]
    (ρ : Representation k G V) (h : Coinvariants.ker ρ = ⊤) :
    IsCover (universalCoverProjection ρ) ∧
      Module.finrank k (universalCoverProjection ρ).toLinearMap.ker =
        Module.finrank k (H1 ρ.dual) :=
  ⟨universalCoverProjection_isCover ρ h, finrank_ker_universalCoverProjection ρ⟩

/-- Every finite-dimensional cover is a quotient of the universal covering,
with the quotient map preserving the projection to the original module. -/
theorem universalCover_factorization [FiniteDimensional k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (p : σ.IntertwiningMap ρ) (hp : IsCover p) :
    ∃ q : (universalAction ρ.dual).dual.IntertwiningMap σ,
      Function.Surjective q ∧ ∀ u, p (q u) = universalCoverProjection ρ u :=
  exists_universalCover_quotient p hp

end CFSG.Quasithin.ChapterI
