module

public import Theory.GroupTheory.PResidual.NormalSup

/-!
# Residual kernel supplements for a normal subgroup with full image

Let a finite p-perfect group map into another group. If a normal
p-perfect subgroup has the whole image, it supplements the p-residual
of the kernel. This is the residual decomposition used in13.7.5(7)
when comparing the automizers of L₁ and L₁,+.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D]

/-- Full image of a normal p-perfect subgroup gives a residual kernel supplement. -/
theorem sup_embedded_pResidual_kernel_eq_top (p : ℕ)
    (X : Subgroup G) [X.Normal] (hG : IsPPerfect p G) (hX : IsPPerfect p X)
    (f : G →* D) (him : X.map f = f.range) :
    X ⊔ (pResidual p f.ker).map f.ker.subtype = ⊤ := by
  have hs : X ⊔ f.ker = ⊤ := by
    have he := congrArg (comap f) him
    simpa only [comap_map_eq, MonoidHom.comap_range_self] using he
  have he := embedded_pResidual_sup_eq_of_normal_sup_top p X f.ker hs
  rwa [(pResidual_eq_top_iff p X).mpr hX,
    (pResidual_eq_top_iff p G).mpr hG, ← MonoidHom.range_eq_map, range_subtype] at he

end Subgroup
