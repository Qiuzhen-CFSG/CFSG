module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Quotients

/-!
# Excluding a nonabelian point span when L₁ is normal

The actual commutator form on U/V₁ is L₁-invariant and has radical
Z(U)/V₁. The natural-seed rank theorem for a normal L₁ forces n≤3
if U is nonabelian. Thus in the remaining n=4,5 nonabelian branch,
the containing point component strictly contains L₁.

Models uses this exclusion on the constructed degree-five point component.
The nonnormal component branches remain with the Section09 source owner.
Source: Aschbacher--Smith, opening of12.9.4, printed p.859.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The normal-L₁ branch of 12.9.4: the original local commutator form
and natural seed rule out nonabelianness in dimensions four and five. -/
theorem point_span_abelian_of_point_residual_normal {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hL1 : ((F.Li L 1).subgroupOf F.H).Normal) : IsMulCommutative F.U := by
  classical
  by_contra hne
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let := hL1
  have hJ := h.point_mem_Hz F earlier.alternatives
  have htwo := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H
    (by omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  have hphi := F.localKernel_frattini_eq_point h.source.simpleQTKE L _ (by omega)
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives) hne
  let := F.tilde_elementary_of_point htwo hphi
  have hcore := F.localKernel_core_le h.source.simpleQTKE L _ F.H
    (by omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  let B := F.tildeBilinearForm (by omega) htwo hphi
  have hB : ∀ (j : F.Li L 1) u v,
      B (Additive.ofMul (F.localTildeAction F.H le_rfl
        ⟨j,(F.Li_le L 1 j.property).2⟩ u.toMul))
        (Additive.ofMul (F.localTildeAction F.H le_rfl
          ⟨j,(F.Li_le L 1 j.property).2⟩ v.toMul)) = B u v := by
    intro j u v
    exact F.tildeBilinearForm_star_invariant (by omega) htwo hphi hcore
      (QuotientGroup.mk' _ ⟨j,(F.Li_le L 1 j.property).2⟩) u.toMul v.toMul
  have hrad : ∀ v : Additive (F.tilde F.U),
      (∀ u, B u v = 0) ↔ (v.toMul : F.G₁tilde) ∈ F.tilde F.ZU := by
    intro v
    have hs := F.tildeBilinearForm_isSymm (by omega) htwo hphi
    have hr := F.tildeBilinearForm_radical (by omega) htwo hphi v.toMul
    have hz : F.tildeToUhat (by omega) v.toMul = 1 ↔
        (v.toMul : F.G₁tilde) ∈ F.tilde F.ZU := by
      change v.toMul ∈ (F.tildeToUhat (by omega)).ker ↔ _
      rw [F.tildeToUhat_ker (by omega)]
      rfl
    change (∀ u, B v u = 0) ↔ _ at hr
    rw [← hz,← hr]
    exact forall_congr' (fun u => by rw [hs.eq u v])
  have hb := F.normal_Li_one_nonabelian_rank_le_three h.naturalMarking h.rank.2 B hB hrad hne
  omega

/-- In the remaining nonabelian branch the containing point component
strictly contains the original point residual. -/
theorem point_residual_lt_of_nonabelian {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) (D : Subgroup G)
    (hLD : F.Li L 1 ≤ D) (hD : (D.subgroupOf F.H).Normal) : F.Li L 1 < D := by
  refine lt_of_le_of_ne hLD ?_
  intro he
  exact hne (point_span_abelian_of_point_residual_normal h hn earlier F (he.symm ▸ hD))

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
