module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.LocalProduct
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.QuotientFusion
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Census

/-!
# Assembly of the residual involution fusion argument

This module combines the actual local-product equivalence, its corrected
E₃₂ cover, reduction through the cubic centralizers, and the four-orbit
block argument. Its target uses the actual two-residual `residualK Z`.

The source result 15.3.61(2) is not yet proved here. The extraspecial orbit
calculation, the cubic reductions and block censuses, and the block
normalizers remain explicit premises of the assembly theorem. Their
construction from 15.3.51–59 is required before that source result can be
asserted. `QuotientFusion` supplies the inner correction for the first
calculation; `LocalProduct` constructs the genuine product equivalence
from commuting factors and the source hyperplane order.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1150–1151.
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03.FusionCore
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
variable {G : Type*} [Group G]

private theorem orderOf_eq_of_conjugateBy {I : Subgroup G} {x y : G}
    (h : ConjugateBy I x y) : orderOf y = orderOf x := by
  obtain ⟨g, _, rfl⟩ := h
  exact (MulAut.conj g).orderOf_eq x

/-- Conditional assembly of the residual cover through the actual fixed lift,
its two E₃₂ planes, and the blocks `C_P(D_i)V`. All local orbit and normalizer
premises must still be constructed from the source configuration. -/
theorem residual_cover_of_local_geometry [Finite G]
    (Z ZS V : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]
    (g : G) (a : centralizerH Z) (z v : G)
    (e : (fixedLift Z ZS a ⊔ V : Subgroup G) ≃* CentralProductModel)
    (D : Fin 2 → Subgroup G)
    (hinside : ∀ x ∈ closureU Z ZS, orderOf x = 2 → IsConj x z ∨ IsConj x v)
    (houtside : ∀ x ∈ residualK Z, x ∉ closureU Z ZS → orderOf x = 2 →
      ∃ y ∈ fixedLift Z ZS a ⊔ V, ConjugateBy (centralizerH Z) x y)
    (hreduce : ∀ i : Fin 2, ∀ x ∈ localPlane (fixedLift Z ZS a ⊔ V) e i,
      orderOf x = 2 → ∃ y,
        (y ∈ closureU Z ZS ∨ y ∈ fusionBlock (pairP Z ZS g) V (D i)) ∧
          ConjugateBy (pairI Z ZS g) x y)
    (census : ∀ i, BlockCensus (pairI Z ZS g) (pairP Z ZS g) V (D i) z v)
    (hmove : ∀ i, ∃ n ∈ normalizer (fusionBlock (pairP Z ZS g) V (D i) : Set G),
      n ∉ normalizer (V : Set G))
    (hsep : ¬ IsConj z v) :
    ∀ x ∈ residualK Z, orderOf x = 2 → IsConj x z ∨ IsConj x v := by
  have hplane (i : Fin 2) (x : G)
      (hx : x ∈ localPlane (fixedLift Z ZS a ⊔ V) e i) (hx2 : orderOf x = 2) :
      IsConj x z ∨ IsConj x v := by
    obtain ⟨y, hy, hxy⟩ := hreduce i x hx hx2
    have hy2 : orderOf y = 2 := (orderOf_eq_of_conjugateBy hxy).trans hx2
    have hycover : IsConj y z ∨ IsConj y v := by
      rcases hy with hy | hy
      · exact hinside y hy hy2
      · apply block_cover_of_census _ _ _ _ z v (census i) (hmove i) hsep y hy
        intro he
        simp [he] at hy2
    exact hycover.imp (hxy.isConj.trans ·) (hxy.isConj.trans ·)
  intro x hx hx2
  by_cases hxU : x ∈ closureU Z ZS
  · exact hinside x hxU hx2
  obtain ⟨y, hy, hxy⟩ := houtside x hx hxU hx2
  have hy2 : orderOf y = 2 := (orderOf_eq_of_conjugateBy hxy).trans hx2
  have hycover : IsConj y z ∨ IsConj y v := by
    rcases localPlane_cover _ e y hy hy2 with h₀ | h₁
    · exact hplane 0 y h₀ hy2
    · exact hplane 1 y h₁ hy2
  exact hycover.imp (hxy.isConj.trans ·) (hxy.isConj.trans ·)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
