module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Symmetry.Containment
/-!
# Moving-neighbor symmetry: MS93 (4.3.7)(ii)

In the asymmetric case, the preceding normal-commutator argument gives
[Vcirc_d,Qₐ ∩ Q_d] = 1. Work now inside the finite stabilizer at d.
The normal subgroup C = C_{Q_d}(Vcirc_d) contains Qₐ ∩ Q_d. The edge
index gives [Q_d:C] ≤ 4, so the genuine SL₃(2) quotient forces the
two-residual to centralize Q_d/C. Thus [Q_d,Ltilde_d] centralizes Vcirc_d.

Also [Vcirc_d,Q_d] is central at d by the preceding local control.
The three-subgroup lemma and residual commutator idempotence now give
[Vcirc_d,Q_d] = 1, contradicting the earlier H-order bound. Transport
of the contrary configuration gives both directions at arbitrary vertices.
Crucially, Qₐ ∩ Q_d is never assumed normal at d; its centralizer overgroup
C supplies the required normal quotient.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.7)(ii), printed p.888; earlier inputs (4.3.1)--(4.3.3).
ProductFacts is the explicit (4.3.7)(i) input. No far clause or later escape
conclusion is used.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The genuine three-subgroup step, using the normal centralizer at d
and the preceding edge index instead of normality of the intersection there. -/
theorem H_eq_bot_of_intersection_centralizes (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    {d : Vertex R} (hd : (cosetGraph R).dist p.a d = 2)
    (hc : ⁅Vcirc R d, Q R p.a ⊓ Q R d⁆ = ⊥) : H R d = ⊥ := by
  have hdc : color R d = false :=
    (color_eq_of_dist_even R p.a d (hd.symm ▸ (by decide : Even 2))).symm.trans p.color_a
  obtain ⟨r, hr⟩ := counterexample_at_vertex p (by omega) d hdc
  obtain ⟨ir⟩ := initial r
  have isection : Nonempty (NaturalSectionAt d (V R d) (Z R d)) := by
    rw [← hr]
    exact ⟨ir.natural_section⟩
  obtain ⟨s⟩ := isection
  let S := stabilizer R d
  let := finite_stabilizer R d
  let Q₀ := (Q R d).subgroupOf S
  let V₀ := (V R d).subgroupOf S
  let W₀ := (Vcirc R d).subgroupOf S
  let I₀ := (Q R p.a ⊓ Q R d).subgroupOf S
  let N := Q₀ ⊓ centralizer (W₀ : Set S)
  let : Q₀.Normal := Q_normal R d
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (V_normalized d)
  let : W₀.Normal := normal_subgroupOf_of_le_normalizer (Vcirc_normalized d)
  have hQG : Q R d ≤ S := fun _ hx => hx.1
  have hVG : V R d ≤ S := (geometry.V_le_Q hb d hdc).trans hQG
  have hWV : Vcirc R d ≤ V R d := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer d).trans (V_normalized d))
  have hWG := hWV.trans hVG
  have hIN : I₀ ≤ N := by
    rintro x hx
    refine ⟨hx.2, ?_⟩
    intro w hw
    apply Subtype.ext
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc) hx) w hw
  obtain ⟨t, hat, hdt⟩ := exists_common_neighbor_of_dist_two R p.a d hd
  have htcol : color R t = true := by
    have hne := adjacent_color_ne R hat
    rw [p.color_a] at hne
    cases h : color R t <;> simp_all
  have hindex : (Q R p.a).relIndex (Q R t) = 4 :=
    (Propagation.edge_indices hb modules p initial control edge p.a t p.color_a hat).2
  have hsmall : N.relIndex Q₀ ≤ 4 := by
    calc
      N.relIndex Q₀ ≤ I₀.relIndex Q₀ :=
        relIndex_le_of_le_left hIN (index_ne_zero_of_finite (H := I₀.subgroupOf Q₀))
      _ = (Q R p.a ⊓ Q R d).relIndex (Q R d) := relIndex_subgroupOf hQG
      _ = (Q R p.a).relIndex (Q R d) := inf_relIndex_right _ _
      _ ≤ (Q R p.a).relIndex (Q R t) :=
        relIndex_le_of_le_right (Q_le_adjacent_h R htcol hdt) (by rw [hindex]; decide)
      _ = 4 := hindex
  let π := s.projection
  have hp : IsPGroup 2 π.ker := by
    rw [s.module_section.projection_kernel]
    exact (Q_isPGroup R source.two_group source.core_le d hdc).comap_subtype
  have hQN : ⁅Q₀, pResidual 2 S⁆ ≤ N :=
    Symmetry.small_normal_section_residual π s.module_section.projection_surjective hp
      Q₀ N inf_le_left s.module_section.projection_kernel.ge hsmall
  have hfirst : ⁅⁅Q₀, pResidual 2 S⁆, W₀⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hQN.trans inf_le_right)
  have hsecond : ⁅⁅W₀, Q₀⁆, pResidual 2 S⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx l hl
    have hx' : (x : FreeAmalgam R) ∈ H R d := by
      have hh := mem_map_of_mem S.subtype hx
      rw [map_commutator, map_subgroupOf_eq_of_le hWG, map_subgroupOf_eq_of_le hQG] at hh
      exact hh
    have hHcenter : H R d ≤ localCenter d :=
      (commutator_mono hWV le_rfl).trans
        (radius_kernel_commutator_le_center source p hb control edge d hdc)
    have hcent := ((le_localCenter_iff d _).mp hHcenter).2 hx'
    apply Subtype.ext
    exact hcent l l.property
  have hthird : ⁅⁅pResidual 2 S, W₀⁆, Q₀⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hsecond hfirst
  have hnative : ⁅V₀, pResidual 2 S⁆ = W₀ := by
    apply map_injective S.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hVG, map_subgroupOf_eq_of_le hWG]
    rfl
  have hfull : ⁅W₀, pResidual 2 S⁆ = W₀ := by
    have h := commutator_isPPerfect_idempotent (pResidual 2 S) V₀
      (isPPerfect_pResidual 2)
      ((Q_isPGroup R source.two_group source.core_le d hdc).to_le
        (geometry.V_le_Q hb d hdc)).comap_subtype le_normalizer_of_normal
    simpa only [hnative] using h
  rw [commutator_comm (pResidual 2 S) W₀, hfull] at hthird
  have hh := congrArg (Subgroup.map S.subtype) hthird
  dsimp only [W₀, Q₀] at hh
  change ⁅Vcirc R d, Q R d⁆ = ⊥
  simpa only [map_commutator, map_subgroupOf_eq_of_le hWG,
    map_subgroupOf_eq_of_le hQG, Subgroup.map_bot] using hh

/-- Reverse movement forces movement, by the asymmetric commutator
calculation and the nontriviality of H at the opposite vertex. -/
theorem moving_of_reverse (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (products : ProductFacts geometry) {d : Vertex R}
    (hm : p.a ∈ movingNeighbors geometry d) : d ∈ movingNeighbors geometry p.a := by
  by_contra hn
  obtain ⟨ip⟩ := initial p
  have hc := asymmetric_intersection_centralizes source p hb modules ip control products hm hn
  have hd : (cosetGraph R).dist p.a d = 2 := by rw [SimpleGraph.dist_comm]; exact hm.1
  have hH := H_eq_bot_of_intersection_centralizes source p hb modules initial control edge hd hc
  have hdc : color R d = false :=
    (color_eq_of_dist_even R d p.a (hm.1.symm ▸ (by decide : Even 2))).trans p.color_a
  obtain ⟨q, hq⟩ := counterexample_at_vertex p (by omega) d hdc
  obtain ⟨iq⟩ := initial q
  have hcard := iq.H_card
  rw [hq, hH, card_bot] at hcard
  omega

/-- Original MS93 (4.3.7)(ii), conditional only on the supplied preceding
stages. Transport discharges the opposite vertex's contrary configuration. -/
theorem moving_symmetric (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (products : ProductFacts geometry) (p : Counterexample geometry) (d : Vertex R) :
    d ∈ movingNeighbors geometry p.a ↔ p.a ∈ movingNeighbors geometry d := by
  constructor
  · intro hm
    have hdc : color R d = false :=
      (color_eq_of_dist_even R p.a d (hm.1.symm ▸ (by decide : Even 2))).symm.trans p.color_a
    obtain ⟨q, rfl⟩ := counterexample_at_vertex p (by omega) d hdc
    exact moving_of_reverse source q hb modules initial control edge products hm
  · exact moving_of_reverse source p hb modules initial control edge products

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
