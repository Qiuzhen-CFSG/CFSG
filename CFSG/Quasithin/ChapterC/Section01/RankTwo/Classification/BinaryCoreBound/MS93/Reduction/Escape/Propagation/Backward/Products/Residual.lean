module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Span
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Algebra

/-!
# Residual action on the selected backward span

Once an edge t generates the starting stabilizer with the critical endpoint
and W(t) lies in Q_c, the join W(t)V_a is normal in that finite stabilizer.
The endpoint escapes Q_a, so its normal closure contains the two-residual
of G_a. The endpoint commutator bound therefore extends to the residual;
residual idempotence sharpens its range from V_a to Vcirc_a.

All quotients and normal closures below are taken inside the finite vertex
group, not inside the free amalgam. The edge choice remains an explicit
premise. Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(i),
printed pp.887--888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : Geometry R}

private theorem commutator_join_normal_le {G : Type*} [Group G]
    (W N J : Subgroup G) [N.Normal] (hc : ⁅W, J⁆ ≤ N) : ⁅W ⊔ N, J⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  have hN : N.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' N).symm
  have hz : (⁅W ⊔ N, J⁆).map q = ⊥ := by
    rw [map_commutator, Subgroup.map_sup, hN, sup_bot_eq, ← map_commutator,
      Subgroup.map_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hc
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz

/-- The residual estimate for the actual normal join at a selected edge. -/
theorem backwardSpan_join_residual_le (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 4 < geometry.b R) (initial : InitialFacts p)
    (t : Vertex R)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a)
    (hW : backwardSpan geometry p.a t ≤ Q R p.c) :
    ⁅backwardSpan geometry p.a t ⊔ V R p.a, Ltilde R p.a⁆ ≤ Vcirc R p.a := by
  let S := stabilizer R p.a
  let := finite_stabilizer R p.a
  let W := (backwardSpan geometry p.a t ⊔ V R p.a).subgroupOf S
  let V₀ := (V R p.a).subgroupOf S
  let J := (Z R p.a').subgroupOf S
  let π := initial.natural_section.projection
  obtain ⟨hWG, hnormal⟩ := backwardSpan_join_normal p hb initial t hgen hW
  let : W.Normal := hnormal
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (V_normalized p.a)
  have hVG : V R p.a ≤ S := initial.natural_section.local_group
  have hJG : Z R p.a' ≤ S := p.end_Z_le_start_stabilizer
  have hW₀G : backwardSpan geometry p.a t ≤ S := le_sup_left.trans hWG
  have hker : IsPGroup 2 π.ker := by
    rw [initial.natural_section.module_section.projection_kernel]
    exact (Q_isPGroup R source.two_group source.core_le p.a p.color_a).comap_subtype
  have hpW : IsPGroup 2 W :=
    ((Q_isPGroup R source.two_group source.core_le p.a p.color_a).to_le
      (sup_le (backwardSpan_le_Q p.color_a hb t)
        (geometry.V_le_Q (by omega) p.a p.color_a))).comap_subtype
  have hJ : ¬ J ≤ π.ker := by
    intro h
    apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
    intro z hz
    have hz' := h (show (⟨z, hJG hz⟩ : S) ∈ J from hz)
    rw [initial.natural_section.module_section.projection_kernel] at hz'
    exact hz'
  have hc₀ : ⁅(backwardSpan geometry p.a t).subgroupOf S, J⁆ ≤ V₀ := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hW₀G, map_subgroupOf_eq_of_le hJG]
    exact (endpoint_commutator_le_radius p (by omega) initial _ hW).trans p.radius_le_start
  have hc : ⁅W, J⁆ ≤ V₀ := by
    dsimp only [W]
    rw [subgroupOf_sup hW₀G hVG]
    exact commutator_join_normal_le _ V₀ J hc₀
  have h := map_mono (f := S.subtype)
    (PairingControl.Geometry.LocalProducts.residual_commutator_bound π
      initial.natural_section.module_section.projection_surjective hker W V₀ J hpW hJ hc)
  dsimp only [W, V₀] at h
  simpa only [map_commutator, map_subgroupOf_eq_of_le hWG,
    map_subgroupOf_eq_of_le hVG, Vcirc, Ltilde, S] using h

/-- Restriction to W(t) retains the sharp residual range Vcirc_a. -/
theorem backwardSpan_residual_le (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 4 < geometry.b R) (initial : InitialFacts p)
    (t : Vertex R)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a)
    (hW : backwardSpan geometry p.a t ≤ Q R p.c) :
    ⁅backwardSpan geometry p.a t, Ltilde R p.a⁆ ≤ Vcirc R p.a :=
  (commutator_mono le_sup_left le_rfl).trans
    (backwardSpan_join_residual_le source p hb initial t hgen hW)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
