module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedMovement

/-!
# Critical center intersections and the opening separation in (10.8)

The actual critical Sylow products identify both critical center/core
intersections with Z_beta. Opposite natural fixed spaces consequently split
Z_alpha into the two neighboring centers, and the original natural coordinates
give |Z_beta| = q_alpha. No beta model or seed saturation is needed.

For the literal residual R_alpha = C_D_alpha(W_alpha), this makes
R_alpha disjoint from Z_alpha'. The subgroup J = R_alpha intersect
Q_(alpha'+1) lies in D_alpha' and has O²(L_alpha') displacement in Z_alpha'.
Its normalizing O²-actors therefore centralize it. The proof keeps this
O²-actor separate from R_alpha; it does not assert J = 1 or full (10.8).

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.1)--(10.2), p.154, (10.4)(c), pp.155--156, and the opening of (10.8),
pp.159--160. BTwoResidualSeparationSource applies the results to the original
F1.11 endpoint cores and the literal reduced-completion inclusion.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem center_core (h : LocallyRankOneTriple P B) (x : Vertex F) :
    Z F x ≤ Q F x := fun _ hz =>
  ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h x).1 hz)).1

private theorem critical_center_core_le_middle
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w : Vertex F}
    (hm : (graph F).Adj v m) (hw : (graph F).Adj m w)
    (hs : Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w)) :
    Z F w ⊓ Q F v ≤ Z F m := by
  let := finite_endpoints h
  have hS := source_kernel_sylow h hB hSyl
  let S := Z F v ⊔ Q F w
  obtain ⟨T,hT⟩ := hs
  have hSE : S ≤ stabilizer F w ⊓ stabilizer F m := by
    apply sup_le
    · exact le_inf
        (Z_le_stabilizer_of_dist_le_b F h.generate v w (by
          have hh := (connected_graph h).dist_triangle (u := v) (v := m) (w := w)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hm,
            SimpleGraph.dist_eq_one_iff_adj.mpr hw] at hh
          simpa only [hb] using hh))
        ((graph_Z_le_Q_of_short h hS (by
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hm,hb]; decide)).trans
          (Q_le_stabilizer F m))
    · exact le_inf (Q_le_stabilizer F w)
        ((source_Z_Q_U h w).2.trans
          ((ballKernel_one_le_edge F hw.symm).trans inf_le_right))
  have hedge : S = (stabilizer F w ⊓ stabilizer F m).pCoreIn 2 :=
    hT.symm.trans (sylow_image_eq_edge_core _ _ inf_le_left
      (source_edge_core_sylow h hB hw.symm) T (hT ▸ hSE))
  obtain ⟨A,hA⟩ := source_edge_vertex_sylow h hSyl hw
  have hAS : (A : Subgroup (stabilizer F m)).map (stabilizer F m).subtype = S := by
    rw [hedge]
    simpa only [inf_comm] using sylow_image_eq_edge_core _ _ inf_le_left
      (source_edge_core_sylow h hB hw) A hA
  have hseed : omegaCenterIn S ≤ Z F m := by
    rw [←hAS]
    exact le_iSup (fun R : Sylow 2 (stabilizer F m) =>
      omegaCenterIn ((R : Subgroup (stabilizer F m)).map (stabilizer F m).subtype)) A
  intro x hx
  apply hseed
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨mem_sup_right (center_core h w hx.1),?_,
    ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w).1 hx.1)).2.2⟩
  have hZ : Z F v ≤ centralizer ({x} : Set G) := by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr (graph_Q_centralizes_Z h v hx.2 z hz)
  have hQ : Q F w ≤ centralizer ({x} : Set G) := by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr ((graph_Q_centralizes_Z h w hz x hx.1).symm)
  intro z hz
  exact mem_centralizer_singleton_iff.mp ((sup_le hZ hQ) hz)


/-- Both critical fixed subgroups, and the intersection of the two
critical centers, equal the literal middle center. -/
theorem BTwoCenterActionData.central_critical_intersections
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m)) :
    Z F v ⊓ Q F w = Z F m ∧ Z F w ⊓ Q F v = Z F m ∧
      Z F v ⊓ Z F w = Z F m := by
  have hm0 := center_le_of_central_neighbor h hB hSyl c.middle hcentral
  have hm1 := center_le_of_central_neighbor h hB hSyl c.terminal.symm hcentral
  have h0 : Z F v ⊓ Q F w = Z F m := le_antisymm
    (critical_center_core_le_middle h hB hSyl hb c.terminal.symm c.middle.symm
      (c.own_critical_product h)) (le_inf hm0 (hm1.trans (center_core h w)))
  have h1 : Z F w ⊓ Q F v = Z F m := le_antisymm
    (critical_center_core_le_middle h hB hSyl hb c.middle c.terminal c.critical_product)
    (le_inf hm1 (hm0.trans (center_core h v)))
  exact ⟨h0,h1,le_antisymm ((inf_le_inf_left _ (center_core h w)).trans h0.le)
    (le_inf hm0 hm1)⟩

/-- The two distinct neighboring centers are the literal direct factors
of the alpha center in (10.2)(c). -/
theorem BTwoCenterActionData.central_neighbor_centers
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    Z F v = Z F m ⊔ Z F t ∧ Disjoint (Z F m) (Z F t) := by
  let := finite_endpoints h
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  have h0 := (c.central_critical_intersections h hB hSyl hb hcentral).1
  have hgv : (g : G) • v = v := c.actor_le g.property
  have h1 : Z F v ⊓ Q F ((g : G) • w) = Z F t := by
    have hh := congrArg (map (MulAut.conj (g : G)).toMonoidHom) h0
    rwa [map_inf _ _ _ (MulAut.conj (g : G)).injective,
      ←Z_translate,←Q_translate,←Z_translate,hgv,hg] at hh
  refine ⟨by simpa only [h0,h1] using d.center_span,?_⟩
  apply disjoint_iff.mpr
  apply bot_unique
  intro x hx
  have hx0 : x ∈ Z F v ⊓ Q F w := h0.symm ▸ hx.1
  have hx1 : x ∈ Z F v ⊓ Q F ((g : G) • w) := h1.symm ▸ hx.2
  have hxc : x ∈ centralizer ((Z F w ⊔ Z F ((g : G) • w) : Subgroup G) : Set G) := by
    have hh : Z F w ⊔ Z F ((g : G) • w) ≤ centralizer ({x} : Set G) := by
      apply sup_le
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr (graph_Q_centralizes_Z h w hx0.2 y hy)
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr
          (graph_Q_centralizes_Z h ((g : G) • w) hx1.2 y hy)
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hh hy)
  exact d.center_fixed_eq_bot h (hd.symm ▸ hω) ▸ ⟨hx0.1,hxc⟩

local instance residualSeparationAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The earlier natural coordinates compute the actual beta-center order. -/
theorem BTwoCenterActionData.central_middle_center_card
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) : Nat.card (Z F m) = Nat.card k := by
  let := finite_endpoints h
  let : Finite (Z F v) := Finite.of_injective
    (inclusion (Z_le_stabilizer F v)) (inclusion_injective _)
  have hz := c.central_center_card E (c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral)
  have hidx := c.line_index E
  have h0 := (c.central_critical_intersections h hB hSyl hb hcentral).1
  have hm : Z F m ≤ Z F v := h0 ▸ inf_le_left
  have hi : (Z F m).relIndex (Z F v) = Nat.card k := by
    rw [←h0,inf_relIndex_left]
    exact hidx
  have hh := ((Z F m).subgroupOf (Z F v)).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hm).toEquiv] at hh
  change (Z F m).relIndex (Z F v) * Nat.card (Z F m) = Nat.card (Z F v) at hh
  rw [hi,hz,pow_two] at hh
  exact Nat.mul_left_cancel (Nat.card_pos : 0 < Nat.card k) hh


/-- The O²-actor moves the actual D subgroup only inside the alpha center,
as used in the proof of (10.8). -/
theorem BTwoCenterActionData.D_residual_commutator_le_center
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    ⁅D F m t,(pResidual 2 c.actor).map c.actor.subtype⁆ ≤ Z F v := by
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  let A := Z F w ⊔ Z F ((g : G) • w)
  let C := commutatorPreimage c.actor (D F m t) (Z F v)
  have hCL : C ≤ c.actor := commutatorPreimage_le _ _ _
  have hnZ : c.actor ≤ normalizer (Z F v : Set G) := c.coordinates.normalized
  have hnD : c.actor ≤ normalizer (D F m t : Set G) := hd ▸ d.normalized h hS hb
  have hnC : c.actor ≤ normalizer (C : Set G) :=
    commutatorPreimage_normalized _ _ _ _ hnZ c.actor.le_normalizer hnD hnZ
  let : (C.subgroupOf c.actor).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCL).mpr hnC
  have hgen : A ⊔ Q F v = c.actor := d.actor_generators.symm.trans hd
  have hAL : A ≤ c.actor := le_sup_left.trans hgen.le
  have hDL : D F m t ≤ c.actor := d.separated.trans c.core_le
  have hZR : ⁅D F m t,A⁆ ≤ Z F v := by
    rw [d.decomposition h hS hb]
    apply commutator_sup_le_of_relative_normal c.actor (Z F v) d.residual A
      (Z F v) hnZ c.coordinates.section_le
      ((inf_le_left.trans inf_le_left).trans hDL)
    · exact le_normalizer_iff_commutator_le_left.mp (hAL.trans hnZ)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr (d.residual_centralizes h)).le.trans bot_le
  have hAC : A ≤ C := le_commutatorPreimage hAL ((commutator_comm A (D F m t)).trans_le hZR)
  have hs : C.subgroupOf c.actor ⊔ (Q F v).subgroupOf c.actor = ⊤ := by
    apply top_unique
    have hh : A.subgroupOf c.actor ⊔ (Q F v).subgroupOf c.actor = ⊤ := by
      rw [←subgroupOf_sup hAL c.core_le,hgen,subgroupOf_self]
    rw [←hh]
    exact sup_le_sup (comap_mono hAC) le_rfl
  have hRC : pResidual 2 c.actor ≤ C.subgroupOf c.actor :=
    sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top _ _
      (isPGroup_pCoreIn 2 (stabilizer F v)).comap_subtype hs⟩
  have hm := map_mono (f := c.actor.subtype) hRC
  rw [map_subgroupOf_eq_of_le hCL] at hm
  rw [commutator_comm]
  exact (commutator_mono hm le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hnZ)

/-- For the actual source residual, the subgroup tested in (10.8) lies
in the terminal D and misses its natural center. This is not the full
assertion that the subgroup itself is trivial. -/
theorem BTwoCenterActionData.residual_separation_prefix
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    ∃ g : c.actor, (g : G) • m = t ∧
      let R := bTwoResidual F m t w ((g : G) • w)
      R ≤ Q F v ∧ R ≤ Q F w ∧ Disjoint R (Z F w) ∧
        ∀ y : Vertex F, R ⊓ Q F y ≤ D F m y ∧ Disjoint (R ⊓ Q F y) (Z F w) := by
  obtain ⟨g,hg,hr,hdec,hdis,_,_,_⟩ := c.central_residual_structure
    h hB hSyl hb hactor hcentral ht hne
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨g',hg',hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hS hb g' hg' hop
  let R := bTwoResidual F m t w ((g : G) • w)
  have hRv : R ≤ Q F v := inf_le_left.trans d.separated
  have hRw : R ≤ Q F w := by
    change bTwoResidual F m t w ((g : G) • w) ≤ Q F w
    rw [hr]
    exact inf_le_left.trans inf_le_right
  have hRZ : Disjoint R (Z F w) := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hxm : x ∈ Z F m :=
      (c.central_critical_intersections h hB hSyl hb hcentral).2.1 ▸ ⟨hx.2,hRv hx.1⟩
    have hxv := center_le_of_central_neighbor h hB hSyl c.middle hcentral hxm
    exact hdis.le_bot ⟨hxv,hx.1⟩
  exact ⟨g,hg,hRv,hRw,hRZ,fun y =>
    ⟨le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right,
      hRZ.mono inf_le_left le_rfl⟩⟩


/-- The terminal two-residual has displacement in Z_alpha'; its part
normalizing the tested intersection centralizes it. No separation
conclusion or Cartan normalization is assumed. -/
theorem BTwoCenterActionData.residual_separation_control
    {k' W' : Type*} [Field k'] [Finite k'] [CharP k' 2]
    [AddCommGroup W'] [Module (ZMod 2) W']
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t y : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (c' : BTwoCenterActionData F w m v k' W')
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hy : (graph F).Adj w y) (hyne : y ≠ m) :
    ∃ g : c.actor, (g : G) • m = t ∧
      let J := bTwoResidual F m t w ((g : G) • w) ⊓ Q F y
      let A := (pResidual 2 c'.actor).map c'.actor.subtype
      J ≤ D F m y ∧ Disjoint J (Z F w) ∧ ⁅J,A⁆ ≤ Z F w ∧
        J ≤ centralizer ((A ⊓ normalizer (J : Set G) : Subgroup G) : Set G) := by
  obtain ⟨g,hg,_,_,_,hJ⟩ := c.residual_separation_prefix h hB hSyl hb hactor hcentral ht hne
  let J := bTwoResidual F m t w ((g : G) • w) ⊓ Q F y
  let A := (pResidual 2 c'.actor).map c'.actor.subtype
  obtain ⟨hJD,hJZ⟩ := hJ y
  have hc : ⁅J,A⁆ ≤ Z F w := (commutator_mono hJD le_rfl).trans
    (c'.D_residual_commutator_le_center h (source_kernel_sylow h hB hSyl) hb hy hyne)
  refine ⟨g,hg,hJD,hJZ,hc,?_⟩
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  apply hJZ.le_bot.trans'
  exact le_inf (le_normalizer_iff_commutator_le_left.mp inf_le_right)
    ((commutator_mono le_rfl inf_le_left).trans hc)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
