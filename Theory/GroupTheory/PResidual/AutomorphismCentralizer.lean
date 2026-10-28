module
public import Theory.GroupTheory.PResidual.Quotient
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# Residual centralization through the automorphism group

A subgroup whose automorphism group is a p-group is centralized by the
p-residual of every group normalizing it. The normalizer conjugation map
has the literal ambient centralizer as kernel.

Source application: Aschbacher–Smith 14.3.20, where the normalized subgroup
is the actual dihedral supplement and p is two.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G]
theorem embedded_pResidual_le_centralizer_of_aut_isPGroup
    (p : ℕ) (H D : Subgroup G) (hn : H ≤ normalizer (D : Set G))
    (ha : IsPGroup p (MulAut D)) :
    (pResidual p H).map H.subtype ≤ centralizer (D : Set G) := by
  let f := D.normalizerMonoidHom.comp (inclusion hn)
  rintro x ⟨y,hy,rfl⟩
  have hh := pResidual_le_ker_of_isPGroup p f ha hy
  change inclusion hn y ∈ D.normalizerMonoidHom.ker at hh
  rw [normalizerMonoidHom_ker] at hh
  exact hh
end Subgroup
