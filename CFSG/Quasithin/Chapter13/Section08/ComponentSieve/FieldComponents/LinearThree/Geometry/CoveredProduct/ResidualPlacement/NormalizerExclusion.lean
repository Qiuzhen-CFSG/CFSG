module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.ComponentAction
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.Commutator.NormalizesSupplement

/-!
# Excluding the central L₀ direction using its source normalizer

Centralization modulo O₂(H) normalizes L₀O₂(H). Since L₀ is two-perfect
and O₂(H) lies in the source Sylow subgroup, which normalizes L₀, the
embedded two-residual of this product is L₀ itself. Thus K* centralizing
L₀* would put K in N_G(L₀) ≤ M, contradicting K ≰ M.

The lift is the same residual argument used by the existing exceptional-field
`Containment.Lifting` module, retained here under narrow imports for this
independent branch. Source: Aschbacher–Smith, 1 March 2004 manuscript,
13.2.2(9), printed p.878, and 13.8.21(1), printed p.957.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_of_star_centralizing (H K C : Subgroup G) (hKH : K ≤ H) (hCH : C ≤ H)
    (hC : IsPPerfect 2 C) (hQC : H.pCoreIn 2 ≤ normalizer (C : Set G))
    (hstar : Source.starImage H K ≤ centralizer (Source.starImage H C : Set (Source.Hstar H))) :
    K ≤ normalizer (C : Set G) := by
  have hC' : IsPPerfect 2 (C.subgroupOf H) :=
    hC.of_surjective (subgroupOfEquivOfLe hCH).symm.toMonoidHom
      (subgroupOfEquivOfLe hCH).symm.surjective
  have hQC' : pCore 2 H ≤ normalizer (C.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hCH]
    intro x hx
    exact hQC (mem_map.mpr ⟨x, hx, rfl⟩)
  have hcomm : ⁅C.subgroupOf H, K.subgroupOf H⁆ ≤ pCore 2 H := by
    rw [← QuotientGroup.ker_mk' (pCore 2 H), ← Subgroup.map_eq_bot_iff, map_commutator,
      commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hstar
  have hr := embedded_pResidual_join_pGroup (C.subgroupOf H) (pCore 2 H)
    hC' pCore_isPGroup hQC'
  have hn := (le_normalizer_sup_of_commutator_le (C.subgroupOf H) (K.subgroupOf H)
    (C.subgroupOf H) (pCore 2 H) le_rfl hcomm).trans
      (normalizer_le_residual_normalizer ((C.subgroupOf H) ⊔ pCore 2 H))
  change K.subgroupOf H ≤ normalizer
    ((pResidual 2 (C.subgroupOf H ⊔ pCore 2 H : Subgroup H)).map
      (C.subgroupOf H ⊔ pCore 2 H).subtype : Set H) at hn
  rw [hr] at hn
  apply le_normalizer_iff.mpr
  intro k hk c hc
  exact le_normalizer_iff.mp hn ⟨k, hKH hk⟩ hk ⟨c, hCH hc⟩ hc

/-- The actual source normalizer bound excludes L₀ as the centralizing
residual direction. Only normality relative to H is used in the lift. -/
theorem zero_not_star_centralizing (H K L T V₁ M : Subgroup G)
    (hKH : K ≤ H) (hDH : one L T V₁ ≤ H)
    (hTL : T ≤ normalizer (L : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hKM : ¬ K ≤ M) (hNM : normalizer (zero L : Set G) ≤ M) :
    ¬ Source.starImage H K ≤ centralizer (Source.starImage H (zero L) : Set (Source.Hstar H)) := by
  intro hc
  have hQT : H.pCoreIn 2 ≤ T := by
    rw [← hS]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal S)
  have hZH := (LocalAction.zero_le_one_of_factorization L T V₁ hfactor).trans hDH
  exact hKM ((normalizes_of_star_centralizing H K (zero L) hKH hZH (residual_isPPerfect _)
    (hQT.trans (hTL.trans (normalizer_le_zero_normalizer L))) hc).trans hNM)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
