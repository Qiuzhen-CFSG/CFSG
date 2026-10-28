module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration.SourceCases
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement.Basic

/-!
# Centralizer geometry through C_D(L) = 1 in 14.4.7

The literal alternatives of 14.4.2 generate the two-residual in the actual
star quotient. Applying those alternatives at the inverse transporter and
lifting through the two-core gives K^g = [K^g,W]. The hyperplane obstruction
and the normalizer consequence of uniqueness then give K^g ≤ C_G(D) and
C_D(L) = 1. `source_centralizer_geometry` assembles these results with the
extraspecial lift and the central commutator bounds. No generation or
centralizer conclusion is assumed.

For the subsequent complement argument, conjugate [D,W] = 1 by a point
stabilizer element in L ∩ H^g. Such an element preserves V, so V₂^t ≤ V,
and C_{U^x}(V) ≤ W^t centralizes D. `complement_bounds` applies this to
the literal three-factor candidate defined by the complement module.

The explicit source inputs are the earlier 12.8/14.3 geometry, the genuine
14.4.2 alternatives with their exact elementary ranks, the involution-rank
dichotomy of 14.4.6, and uniqueness over LT^g. The point-stabilizer orbit
is the earlier natural L₃(2)-action from 14.3.16; its witnesses stay in L.
Their discharge belongs to the outer source assembly. The Sylow property,
Gaschütz complement and final equality U = O₂(H) are separate deductions.

Source: Aschbacher--Smith, 14.4.7, printed pp.1008--1009.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
open Subgroup
variable {G : Type*} [Group G]

/-- Transport the fixed-point bound using the point stabilizer inside L. -/
theorem symmetric_fixed_centralizers (H U A V₂ L V₀ : Subgroup G) (g : G)
    (hH : H = normalizer (A : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hV₂V : V₂ ≤ V₀) (hLV : L ≤ normalizer (V₀ : Set G))
    (hpoints : ∀ x ∈ L, conjugate A x = conjugate A g ∨
      ∃ t ∈ L, t ∈ conjugate H g ∧ conjugate A x = conjugate A t)
    (hcomm : ⁅D H U g, W U V₂⁆ = ⊥) :
    ∀ x ∈ L, conjugate U x ⊓ centralizer (V₀ : Set G) ≤
      centralizer (D H U g : Set G) := by
  have hHgD : conjugate H g ≤ normalizer (D H U g : Set G) :=
    relative_centralizer_normalized _ _ (conjugate_normalizes H U g hHU)
  have hWD : W U V₂ ≤ centralizer (D H U g : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  intro x hx
  rcases hpoints x hx with he | ⟨t, htL, htH, he⟩
  · rw [conjugate_eq_of_center_eq H U A hH hHU x g he]
    exact inf_le_left.trans (le_centralizer_iff.mp (show D H U g ≤
      centralizer (conjugate U g : Set G) from inf_le_right))
  · have hplane : conjugate V₂ t ≤ V₀ := by
      have hh : conjugate V₂ t ≤ conjugate V₀ t := map_mono hV₂V
      rwa [conjugate_eq_self V₀ (hLV htL)] at hh
    have hfixed : conjugate (W U V₂) t ≤ centralizer (D H U g : Set G) := by
      have hh : conjugate (W U V₂) t ≤ conjugate (centralizer (D H U g : Set G)) t :=
        map_mono hWD
      rwa [conjugate_centralizer, conjugate_eq_self (D H U g) (hHgD htH)] at hh
    have hW : conjugate (W U V₂) t =
        conjugate U t ⊓ centralizer (conjugate V₂ t : Set G) := by
      unfold W conjugate
      rw [map_inf _ _ _ (MulAut.conj t⁻¹).injective, centralizer_map]
    rw [conjugate_eq_of_center_eq H U A hH hHU x t he]
    exact (inf_le_inf_left _ (centralizer_le hplane)).trans (hW ▸ hfixed)

variable {V : Type*} [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {H U A V₂ L : Subgroup G} {g : G} [(U.subgroupOf H).Normal]

omit [Module.Finite (ZMod 2) V] in
/-- The source models give generation of the actual ambient conjugate residual. -/
theorem EarlierGeometry.residual_generation_of_source_models
    (d : EarlierGeometry (V := V) H U A V₂ L g)
    (h1442 : ∀ t ∈ L, t ∈ normalizer (V₂ : Set G) → t ∉ H →
      let X := ((conjugate (W U V₂) t).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
      ModelGeneration.SourceAlternative X (Module.finrank (ZMod 2) V) ∧
        IsElementaryAbelian 2 X ∧ Nat.card X = 2 ^ (Module.finrank (ZMod 2) V / 2 - 1)) :
    conjugate ((pResidual 2 H).map H.subtype) g =
      ⁅conjugate ((pResidual 2 H).map H.subtype) g, W U V₂⁆ := by
  obtain ⟨hm, he, hc⟩ := h1442 g⁻¹ (L.inv_mem d.g_mem_L)
    ((normalizer (V₂ : Set G)).inv_mem d.g_normalizes)
    (fun h => d.g_not_mem_H (by simpa only [inv_inv] using H.inv_mem h))
  have hWJ : W U V₂ ≤ conjugate H g := by
    rw [d.H_eq_centralizer, conjugate_centralizer]
    exact inf_le_right.trans (centralizer_le d.conjugate_line_le_plane)
  rw [conjugate_residual]
  exact ambient_residual_generation _ _ hWJ
    (ModelGeneration.star_generation_transport H (W U V₂) g (hm.generation he hc))

/-- The first paragraph of 14.4.7, from the stated earlier-source inputs and
the independent involution-rank dichotomy. -/
theorem EarlierGeometry.source_centralizer_geometry [IsExtraspecial 2 U]
    (d : EarlierGeometry (V := V) H U A V₂ L g)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.action.movedRank a ∨ (d.action.movedRank a = 2 ∧
        ¬ d.action.image (V₂.subgroupOf H) ≤ d.action.moved a))
    (h1442 : ∀ t ∈ L, t ∈ normalizer (V₂ : Set G) → t ∉ H →
      let X := ((conjugate (W U V₂) t).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
      ModelGeneration.SourceAlternative X (Module.finrank (ZMod 2) V) ∧
        IsElementaryAbelian 2 X ∧ Nat.card X = 2 ^ (Module.finrank (ZMod 2) V / 2 - 1))
    (T M : Subgroup G) (hTH : T ≤ H) (hTL : T ≤ normalizer (L : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ conjugate T g ≤ N → N = M)
    (hKM : ¬ conjugate ((pResidual 2 H).map H.subtype) g ≤ M) :
    conjugate (H.pCoreIn 2) g = conjugate U g ⊔ D H U g ∧
      D H U g ≤ H ∧ D H U g ≤ H.pCoreIn 2 ∧
      ⁅D H U g, U⁆ ≤ A ∧ ⁅D H U g, W U V₂⁆ = ⊥ ∧
      conjugate ((pResidual 2 H).map H.subtype) g =
        ⁅conjugate ((pResidual 2 H).map H.subtype) g, W U V₂⁆ ∧
      conjugate ((pResidual 2 H).map H.subtype) g ≤ centralizer (D H U g : Set G) ∧
      D H U g ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨hcore, hcomm, hW⟩ := d.centralizer_bounds hrank
  obtain ⟨hK, hC⟩ := d.centralizer_eq_bot_of_source_models hrank h1442 T M hTH hTL hunique hKM
  exact ⟨d.core_lift, conjugate_D_le H U A V₂ g d.H_eq_centralizer d.A_le_V₂
    d.plane_le_conjugate, hcore, hcomm, hW,
    d.residual_generation_of_source_models h1442, hK, hC⟩

/-- The symmetric bounds and the actual candidate-centralizer application
needed by the subsequent Sylow/Gaschütz deduction. -/
theorem EarlierGeometry.complement_bounds [IsExtraspecial 2 U]
    (d : EarlierGeometry (V := V) H U A V₂ L g)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.action.movedRank a ∨ (d.action.movedRank a = 2 ∧
        ¬ d.action.image (V₂.subgroupOf H) ≤ d.action.moved a))
    (V₀ : Subgroup G) (hV₂V : V₂ ≤ V₀) (hLV : L ≤ normalizer (V₀ : Set G))
    (hpoints : ∀ x ∈ L, conjugate A x = conjugate A g ∨
      ∃ t ∈ L, t ∈ conjugate H g ∧ conjugate A x = conjugate A t) :
    (∀ x ∈ L, ⁅D H U g, conjugate U x⁆ ≤ conjugate A x ∧ conjugate A x ≤ V₀) ∧
      W U V₂ ≤ centralizer (D H U g : Set G) ∧
      (∀ x ∈ L, conjugate U x ⊓ centralizer (V₀ : Set G) ≤
        centralizer (D H U g : Set G)) ∧
      (∀ l ∈ L, GaschutzComplement.candidateSylow U V₀ V₂ g l ≤
        centralizer (GaschutzComplement.conjugateCentralizer H U g : Set G)) := by
  have hDW := (d.centralizer_bounds hrank).2.2
  have hW : W U V₂ ≤ centralizer (D H U g : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hDW)
  have hfixed := symmetric_fixed_centralizers H U A V₂ L V₀ g d.H_eq_normalizer
    d.normalizes hV₂V hLV hpoints hDW
  refine ⟨d.symmetric_bounds hrank V₀ (d.A_le_V₂.trans hV₂V) hLV ?_, hW, hfixed, ?_⟩
  · intro x hx
    rcases hpoints x hx with he | ⟨t, _, ht, he⟩
    · exact Or.inl he
    · exact Or.inr ⟨t, ht, he⟩
  · intro l hl
    exact GaschutzComplement.candidate_centralizes H U V₀ V₂ g l hW (hfixed l hl)
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
