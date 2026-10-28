module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.Assembly
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Discharging the residual placement in the centralizer argument

The actual Sylow subgroup T supplements O²(H) inside H. Since T ≤ M
and H ≰ M by 12.8.3(4), O²(H) cannot lie in M. Right conjugation by
g ∈ L ≤ M preserves this noncontainment. Moreover LT^g = LT because
g ∈ L, so the earlier uniqueness of M over LT is exactly the uniqueness
needed for the normalizer of C_D(L).

The final endpoint therefore assumes neither residual noncontainment nor
a centralizer or generation conclusion. Its inputs are the earlier source
geometry, the literal 14.4.2 alternatives and ranks, the independent 14.4.6
rank dichotomy, the actual Sylow placement, and 14.3.3(2) uniqueness.
This argument does not require M = LT or identify M/O₂(M): the equality
M = LT established in the d = 4 branch is unavailable here.

Source: Aschbacher--Smith, 12.8.3(4), 14.3.3(1)--(2), and the first
paragraph of 14.4.7, printed pp.849--850,990,1008--1009.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
open Subgroup ModelGeneration
variable {G : Type*} [Group G] [Finite G]

private theorem conjugate_residual_not_le_of_sylow (H M : Subgroup G) (T : Sylow 2 G)
    (g : G) (hTH : (T : Subgroup G) ≤ H) (hTM : (T : Subgroup G) ≤ M)
    (hgM : g ∈ M) (hHM : ¬ H ≤ M) :
    ¬ conjugate ((pResidual 2 H).map H.subtype) g ≤ M := by
  have hgen : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (Subgroup.map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
    rwa [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
      ← MonoidHom.range_eq_map, range_subtype] at hh
  intro hKg
  have hK : (pResidual 2 H).map H.subtype ≤ M := by
    have hh : conjugate (conjugate ((pResidual 2 H).map H.subtype) g) g⁻¹ ≤
        conjugate M g⁻¹ := map_mono hKg
    rwa [conjugate_conjugate, mul_inv_cancel, conjugate_one,
      conjugate_eq_self M (M.le_normalizer (M.inv_mem hgM))] at hh
  exact hHM (hgen ▸ sup_le hK hTM)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {H U A V₂ L : Subgroup G} {g : G} [(U.subgroupOf H).Normal]

/-- The source centralizer endpoint, with residual noncontainment proved from
12.8.3(4) and the actual Sylow subgroup, and uniqueness transported from LT. -/
theorem EarlierGeometry.source_centralizer_geometry_of_sylow [IsExtraspecial 2 U]
    (d : EarlierGeometry (V := V) H U A V₂ L g)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.action.movedRank a ∨ (d.action.movedRank a = 2 ∧
        ¬ d.action.image (V₂.subgroupOf H) ≤ d.action.moved a))
    (h1442 : ∀ t ∈ L, t ∈ normalizer (V₂ : Set G) → t ∉ H →
      let X := ((conjugate (W U V₂) t).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
      SourceAlternative X (Module.finrank (ZMod 2) V) ∧
        IsElementaryAbelian 2 X ∧ Nat.card X = 2 ^ (Module.finrank (ZMod 2) V / 2 - 1))
    (T : Sylow 2 G) (M : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hLM : L ≤ M) (hHM : ¬ H ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M) :
    conjugate (H.pCoreIn 2) g = conjugate U g ⊔ D H U g ∧
      D H U g ≤ H ∧ D H U g ≤ H.pCoreIn 2 ∧
      ⁅D H U g, U⁆ ≤ A ∧ ⁅D H U g, W U V₂⁆ = ⊥ ∧
      conjugate ((pResidual 2 H).map H.subtype) g =
        ⁅conjugate ((pResidual 2 H).map H.subtype) g, W U V₂⁆ ∧
      conjugate ((pResidual 2 H).map H.subtype) g ≤ centralizer (D H U g : Set G) ∧
      D H U g ⊓ centralizer (L : Set G) = ⊥ := by
  have hjoin : L ⊔ conjugate (T : Subgroup G) g = L ⊔ (T : Subgroup G) := by
    have hh := conjugate_eq_self (L ⊔ (T : Subgroup G))
      ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left d.g_mem_L))
    rw [conjugate, Subgroup.map_sup] at hh
    change conjugate L g ⊔ conjugate (T : Subgroup G) g = L ⊔ (T : Subgroup G) at hh
    rwa [conjugate_eq_self L (L.le_normalizer d.g_mem_L)] at hh
  exact d.source_centralizer_geometry hrank h1442 (T : Subgroup G) M hTH hTL
    (by simpa only [hjoin] using hunique)
    (conjugate_residual_not_le_of_sylow H M T g hTH hTM (hLM d.g_mem_L) hHM)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
