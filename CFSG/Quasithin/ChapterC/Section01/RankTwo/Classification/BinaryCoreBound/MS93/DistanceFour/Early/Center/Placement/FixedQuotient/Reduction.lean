module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.FixedQuotient.Normalization
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.FixedQuotient.Contract
/-!
# Applying the finite fixed-preimage calculation at the selected edge

The source local generation, commutator bound and edge index identify all
finite-group inputs. The entire actor Q_b lies in G_d, its image has order
four in the natural section's own projection, and its full normalizer
preserves V_b. The cover supplies a nonzero moving vector in V_b.
The full quotient-fixed preimage is exactly B_d, with the actual inclusions.

The final theorem is conditional on NaturalFixedCalculation for this finite
stabilizer. All its source-specific premises are discharged here. This is
not an unconditional proof of the fixed-space equality in (4.6.7).
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.881 and 904.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
open NaturalStructure.Exclusion
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Kernel fixation extends the defining residual fixed preimage to the
whole local stabilizer, retaining the literal quotient map. -/
theorem full_fixed_map_eq_B (common : CommonFacts R source geometry)
    (edge : EdgeFacts R) (d : Vertex R) (hd : color R d = false) :
    letI := geometry.Z_normal d
    (centralizerModulo ((V R d).subgroupOf (stabilizer R d)) ⊤
      ((Z R d).subgroupOf (stabilizer R d))).map (stabilizer R d).subtype =
      B R d (geometry.Z_normal d) := by
  let := geometry.Z_normal d
  have hVS := (radius_le_Q common d hd).trans (show Q R d ≤ stabilizer R d from fun _ hx => hx.1)
  apply le_antisymm
  · rintro x ⟨v, hv, rfl⟩
    obtain ⟨hv, hc⟩ := mem_centralizerModulo_iff.mp hv
    apply (mem_B_iff R d (geometry.Z_normal d) hVS v).mpr
    refine ⟨hv, ?_⟩
    intro l hl
    obtain ⟨l, _, rfl⟩ := hl
    exact hc l (mem_top l)
  · intro x hx
    refine ⟨⟨x, hVS (B_le_radius common d hd hx)⟩, ?_, rfl⟩
    apply mem_centralizerModulo_iff.mpr
    refine ⟨B_le_radius common d hd hx, ?_⟩
    intro g _
    have hcomm := B_commutator_stabilizer_le_Z common edge d hd
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator g.property hx)

/-- Apply the universal finite local calculation to the actual incident kernel.
The finite calculation is the only premise not discharged by source facts here. -/
theorem seed_fixed_quotient_of_calculation (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hseed : ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥)
    (calculation : NaturalFixedCalculation (stabilizer R d)) :
    radiusFixed geometry d (Q R b) =
      (V R b ⊓ Vcirc R d) ⊔ B R d (geometry.Z_normal d) := by
  have hd := seed_color a b d ha hab hdb
  obtain ⟨s⟩ := natural_section_of_seed common hb edge a b d ha hab hdb hseed
  let S := stabilizer R d
  let H := (V R d).subgroupOf S
  let N := (Z R d).subgroupOf S
  let K := (Q R d).subgroupOf S
  let T := pResidual 2 S
  let E := (V R b).subgroupOf S
  let J := (Q R b).subgroupOf S
  have hVS : V R d ≤ S := (radius_le_Q common d hd).trans (fun _ hx => hx.1)
  have hES : V R b ≤ S := (edge_radius_le_radius hd hdb).trans hVS
  have hJS : Q R b ≤ S := edge_actor_le_stabilizer b d hdb
  have hKS : Q R d ≤ S := fun _ hx => hx.1
  have hNS : Z R d ≤ S := Z_le_stabilizer R d
  have hmove : (⁅H, T⁆).map S.subtype = Vcirc R d := by
    rw [map_commutator, map_subgroupOf_eq_of_le hVS]
    rfl
  have hgen : T ⊔ K = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKS,
      ← MonoidHom.range_eq_map, range_subtype]
    exact source.local_generation d hd
  have hcomm : ⁅H, K⁆ ≤ N := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hVS, map_subgroupOf_eq_of_le hKS]
    exact edge.commutator_le_Z d hd
  have hcolb : color R b = true := by
    have hn := adjacent_color_ne R hdb
    cases hc : color R b <;> simp_all
  have hKJ : K ≤ J := subgroupOf_mono _ (Q_le_adjacent_h R hcolb hdb)
  have hcard : Nat.card (J.map s.projection) = 4 := by
    rw [← relIndex_ker, s.module_section.projection_kernel, relIndex_subgroupOf hJS]
    exact edge.edge_Q_index d b hd hdb
  have hNE : N ≤ E := subgroupOf_mono _ (le_iSup_of_le d (le_iSup_of_le
    (show (cosetGraph R).dist d b ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdb)).le.trans
        (by decide)) le_rfl))
  have hEH : E ≤ H := subgroupOf_mono _ (edge_radius_le_radius hd hdb)
  have hfix : ⁅E, J⁆ ≤ N := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hES, map_subgroupOf_eq_of_le hJS,
      commutator_comm]
    apply commutator_le.mpr
    intro g hg x hx
    exact ((mem_radiusFixed_iff common d hd (Q R b) hJS x).mp
      (edge_radius_le_fixed common edge d b hd hdb hx)).2 g hg
  have hnorm : normalizer (J : Set S) ≤ normalizer (E : Set S) := by
    change normalizer ((Q R b).comap S.subtype : Set S) ≤
      normalizer ((V R b).comap S.subtype : Set S)
    rw [← comap_normalizer_eq_of_le_range (hJS.trans_eq S.range_subtype.symm),
      ← comap_normalizer_eq_of_le_range (hES.trans_eq S.range_subtype.symm)]
    exact comap_mono (edge_kernel_normalizer_le_radius_normalizer common d b hd hdb)
  have hout : ¬ E ⊓ (N ⊔ ⁅H, T⁆) ≤ N := by
    intro h
    have hh := map_mono (f := S.subtype) h
    rw [Subgroup.map_inf _ _ _ S.subtype_injective, Subgroup.map_sup,
      map_subgroupOf_eq_of_le hES, map_subgroupOf_eq_of_le hNS, hmove, sup_comm] at hh
    exact seed_edge_moving_not_le_Z common hb edge a b d ha hab hdb hseed hh
  have h := calculation s.projection K T H N E J s.module_section
    hgen hcomm hKJ hcard hNE hEH hfix hnorm hout
  let := geometry.Z_normal d
  have hh := congrArg (Subgroup.map S.subtype) h
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ S.subtype_injective,
    map_subgroupOf_eq_of_le hES, hmove] at hh
  change radiusFixed geometry d (Q R b) = (V R b ⊓ Vcirc R d) ⊔
    (centralizerModulo H ⊤ N).map S.subtype at hh
  rw [full_fixed_map_eq_B common edge d hd] at hh
  exact hh
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
