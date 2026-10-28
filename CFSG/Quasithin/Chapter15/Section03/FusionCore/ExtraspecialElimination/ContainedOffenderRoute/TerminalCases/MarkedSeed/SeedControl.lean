module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SeedPoint
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction

/-!
# Lifting the terminal vector stabilizer to the source seed

A proper seed point has nonzero image in Z_S/Z. Since [Z_S:Z] = 2,
that seed together with Z generates Z_S. Its stabilizer in H/O₂(H)
therefore lifts to a subgroup normalizing Z_S, and 15.3.46(5) places
it in M. This uses the representative formula of the original action;
no new action or complement is chosen.

The compatible orthogonal action and its fixed-plane normalizer calculation
put the lifted stabilizer's two-residual in C_M(V). The ambient Sylow
subgroup supplements that residual. These are bounds and a factorization,
not yet the equality with Y₀T: theta-generation of the component's Sylow
overgroups supplies the remaining step in `MarkedSeed`.

The only extra premise for the normalizer bound is [Z_S:Z] = 2, the order
of the actual quotient in 15.3.48. The residual bound additionally uses
the natural orthogonal action of 15.3.2(1) and the identification
Z_S = C_V(N_T(V_i)) following 15.3.4. Normalization of Z is already
part of the literal SectionAction, so centralization and |Z| = 2 are
unnecessary for these conclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122, 1141–1144, especially the paragraph preceding 15.3.49(k).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases
open ReducedModels ComponentReduction ModelReduction BinaryModels ModelExclusions
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    {r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper}

namespace SeedPoint

def liftedStabilizer (p : SeedPoint r) : Subgroup G :=
  ((pointStabilizer p.space.toRepresentation p.point).comap
    (QuotientGroup.mk' (pCore 2 H))).map H.subtype

theorem liftedStabilizer_le (p : SeedPoint r) : p.liftedStabilizer ≤ H := map_subtype_le _

theorem base_le_liftedStabilizer (p : SeedPoint r) : Y0 ⊔ T ≤ p.liftedStabilizer := by
  apply sup_le
  · intro y hy
    exact ⟨⟨y, r.y_le hy⟩, p.base_le (mem_sup_left ⟨⟨y, r.y_le hy⟩, hy, rfl⟩), rfl⟩
  · intro t ht
    exact ⟨⟨t, r.t_le ht⟩, p.base_le (mem_sup_right ⟨⟨t, r.t_le ht⟩, ht, rfl⟩), rfl⟩

theorem star_liftedStabilizer (p : SeedPoint r) :
    starImage H p.liftedStabilizer = pointStabilizer p.space.toRepresentation p.point := by
  unfold starImage liftedStabilizer Subgroup.subgroupOf
  rw [comap_map_eq_self_of_injective H.subtype_injective,
    map_comap_eq_self (by intro x _; exact QuotientGroup.mk'_surjective _ x)]

theorem seed_not_mem_line (p : SeedPoint r) : (p.seed : G) ∉ Z := by
  intro hz
  have he : QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
      ⟨(p.seed : G), le_conjugateSpanBy ZS H p.seed.property⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hz
  apply p.proper
  rw [p.source_stabilizer, he]
  exact top_unique (fun _ _ => map_zero _)

private theorem line_sup_seed [Finite G] (p : SeedPoint r)
    (hi : Z.relIndex ZS = 2) : Z ⊔ zpowers (p.seed : G) = ZS := by
  have hs : Z ⊔ zpowers (p.seed : G) ≤ ZS :=
    sup_le r.placed.line_le_seed (zpowers_le.mpr p.seed.property)
  have hm := relIndex_mul_relIndex Z (Z ⊔ zpowers (p.seed : G)) ZS le_sup_left hs
  rw [hi] at hm
  have hp : (Z.relIndex (Z ⊔ zpowers (p.seed : G)) *
      (Z ⊔ zpowers (p.seed : G)).relIndex ZS).Prime := hm ▸ Nat.prime_two
  rcases Nat.prime_mul_iff.mp hp with h | h
  · exact le_antisymm hs (relIndex_eq_one.mp h.2)
  · exact (p.seed_not_mem_line ((relIndex_eq_one.mp h.2)
      (mem_sup_right (mem_zpowers (p.seed : G))))).elim

theorem liftedStabilizer_normalizes_seed [Finite G] (p : SeedPoint r)
    (hi : Z.relIndex ZS = 2) : p.liftedStabilizer ≤ normalizer (ZS : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg z hz
  obtain ⟨h, hh, rfl⟩ := hg
  have hh' := hh
  change QuotientGroup.mk' (pCore 2 H) h ∈
    pointStabilizer p.space.toRepresentation p.point at hh'
  rw [p.source_stabilizer] at hh'
  change r.placed.action.representation (QuotientGroup.mk' (pCore 2 H) h) _ = _ at hh'
  rw [r.placed.action.on_representatives] at hh'
  have hc := QuotientGroup.eq_iff_div_mem.mp (congrArg Additive.toMul hh')
  change ((h : G) * (p.seed : G) * (h : G)⁻¹) / (p.seed : G) ∈ Z at hc
  have hs : (h : G) * (p.seed : G) * (h : G)⁻¹ ∈ ZS := by
    simpa only [div_mul_cancel] using
      ZS.mul_mem (r.placed.line_le_seed hc) p.seed.property
  have hmap : ZS.map (MulAut.conj (h : G)).toMonoidHom ≤ ZS := by
    rw [← p.line_sup_seed hi, Subgroup.map_sup]
    apply sup_le
    · exact (mem_normalizer_iff_map_conj_eq.mp
        (r.placed.action.normalizes_layer h.property)).le.trans le_sup_left
    · rw [MonoidHom.map_zpowers]
      apply zpowers_le.mpr
      change (h : G) * (p.seed : G) * (h : G)⁻¹ ∈ _
      rw [p.line_sup_seed hi]
      exact hs
  exact hmap (mem_map_of_mem _ hz)

theorem liftedStabilizer_le_M [Finite G] (p : SeedPoint r)
    (hi : Z.relIndex ZS = 2) : p.liftedStabilizer ≤ M :=
  (p.liftedStabilizer_normalizes_seed hi).trans r.placed.seed_normalizer

theorem stabilizer_le_star_intersection [Finite G] (p : SeedPoint r)
    (hi : Z.relIndex ZS = 2) :
    pointStabilizer p.space.toRepresentation p.point ≤ starImage H (M ⊓ H) := by
  rw [← p.star_liftedStabilizer]
  exact map_mono (comap_mono (le_inf (p.liftedStabilizer_le_M hi) p.liftedStabilizer_le))

theorem liftedStabilizer_residual_le_centralizer [Finite G] (p : SeedPoint r)
    (hi : Z.relIndex ZS = 2) (d : Section03.NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex)
    (hfixed : ZS = fixedPlane V (planeStabilizer r.sylow (d.plane i))) :
    Stellmacher.twoResidualAmbient p.liftedStabilizer ≤ M ⊓ centralizer (V : Set G) := by
  have hTM : (r.sylow : Subgroup G) ≤ M := by
    rw [r.sylow_eq]
    exact r.placed.t_le_m
  have himage : d.image p.liftedStabilizer ≤ d.image (r.sylow : Subgroup G) := by
    rintro a ⟨m, hm, rfl⟩
    apply (CosetSetup.ExtraspecialLocal.NormalizerAction.normalizes_fixedPlane_iff
      d r.sylow hTM i m).mp
    rw [← hfixed]
    exact p.liftedStabilizer_normalizes_seed hi hm
  exact d.residual_le_centralizer_of_image_isTwoGroup (p.liftedStabilizer_le_M hi)
    (((r.sylow.isPGroup'.comap_subtype (K := M)).map d.actor).to_le himage)

theorem liftedStabilizer_residual_sup_sylow [Finite G] (p : SeedPoint r) :
    Stellmacher.twoResidualAmbient p.liftedStabilizer ⊔ T = p.liftedStabilizer := by
  have hT : (r.sylow : Subgroup G) ≤ p.liftedStabilizer := by
    rw [r.sylow_eq]
    exact le_sup_right.trans p.base_le_liftedStabilizer
  simpa only [r.sylow_eq] using residual_sup_sylow r.sylow hT

end SeedPoint
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases
