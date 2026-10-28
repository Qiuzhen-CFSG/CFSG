module
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Sylow-normalized perfect subgroups in an abelian residual

A p-perfect subgroup lies in the p-residual. If that residual is abelian,
it centralizes the subgroup. An ambient Sylow p-subgroup supplements the
residual, so Sylow normalization is enough for full normality.

This is used to exclude an abelian residual in the actual point-span action
in Aschbacher--Smith 13.2.12, printed p.882.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem normal_of_pPerfect_of_abelian_residual (S : Sylow p G)
    [IsMulCommutative (pResidual p G)] (K : Subgroup G)
    (hp : IsPPerfect p K) (hn : (S : Subgroup G) ≤ normalizer (K : Set G)) : K.Normal := by
  have hK : K ≤ pResidual p G := le_pResidual_of_isPPerfect K hp
  have hc : pResidual p G ≤ centralizer (K : Set G) := by
    intro r hr k hk
    exact congrArg (pResidual p G).subtype
      (mul_comm (⟨k,hK hk⟩ : pResidual p G) (⟨r,hr⟩ : pResidual p G))
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←pResidual_sup_sylow_eq_top S]
  exact sup_le (hc.trans (Subgroup.centralizer_le_normalizer _)) hn
end Subgroup
