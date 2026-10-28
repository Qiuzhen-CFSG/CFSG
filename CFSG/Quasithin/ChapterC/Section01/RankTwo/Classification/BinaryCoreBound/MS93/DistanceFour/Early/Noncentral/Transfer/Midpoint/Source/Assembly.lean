module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Midpoint.Source.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Midpoint.Source.Orbit

/-!
# Source midpoint centrality in the second MS93 (4.6.6)

The relative normalizer acts on the actual edge kernel. Its two conjugate
planes generate the edge layer modulo the local center, and a selected actor
has fixed index two. The retained-line comparison supplies a central line in
the moved plane. Holomorph realization gives a genuine adjacent representative
with the same local subgroups and center intersection. Applying the comparison
to this reversed pair supplies the central-product witness; the proved
fixed-index inequality then contradicts the marked edge index four.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), second assertion numbered (4.6.6), printed pp.903--904.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
open Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace Midpoint.Source

private theorem embedded_center_normalizes {G : Type*} [Group G]
    (A H : Subgroup G) (hAH : A ≤ H) :
    (center H).map H.subtype ≤ normalizer A := by
  have hcentral : (center H).map H.subtype ≤ centralizer (A : Set G) := by
    rintro x ⟨z, hz, rfl⟩ y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hAH hy⟩)
  exact hcentral.trans (Subgroup.centralizer_le_normalizer _)

omit [Finite M] in
private theorem conjugate_plane_le_edge_Z
    (edge : EdgeFacts R) (d b : Vertex R) (hd : color R d = false)
    (hdb : Adjacent R d b) (h : FreeAmalgam R)
    (hh : h ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    ⁅Z R (act R h d), Q R b⁆ ≤ Z R b := by
  have hb : color R b = true := by
    have hn := adjacent_color_ne R hdb
    cases hx : color R b <;> simp_all
  have hE : (Z R b).map (MulAut.conj h⁻¹).toMonoidHom = Z R b :=
    mem_normalizer_iff_map_conj_eq.mp
      (edge_normalizer_normalizes_Z b hb ((normalizer _).inv_mem hh))
  rw [edge_plane_act d b h hh]
  exact (map_mono (edge.edge_commutator_le_Z d b hd hdb)).trans_eq hE

omit [Finite M] in
private theorem conjugate_plane_card
    (edge : EdgeFacts R) (d b : Vertex R) (hd : color R d = false)
    (hdb : Adjacent R d b) (h : FreeAmalgam R)
    (hh : h ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    Nat.card (⁅Z R (act R h d), Q R b⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  rw [edge_plane_act d b h hh,
    ← Nat.card_congr ((⁅Z R d, Q R b⁆).equivMapOfInjective
      (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective).toEquiv]
  exact edge.edge_commutator_card d b hd hdb

/-- The source conjugates give the central-product conclusion whenever a
nontrivial retained line is central in the second local group. -/
private theorem center_span_of_retained_line
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (edge : EdgeFacts R) (d c b : Vertex R) (hd : color R d = false)
    (hc : color R c = false) (hdb : Adjacent R d b) (hcb : Adjacent R c b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype)
    (C : Subgroup (FreeAmalgam R)) (hcard : Nat.card C = 2)
    (hC : C ≤ ⁅Z R d, Q R b⁆ ⊓
      (center (stabilizer R c)).map (stabilizer R c).subtype)
    (hnot : ¬ ⁅Z R d, Q R b⁆ ≤
      (center (stabilizer R c)).map (stabilizer R c).subtype) :
    Z R b = (Z R b ⊓ (center (stabilizer R d)).map (stabilizer R d).subtype) ⊔
      (Z R b ⊓ (center (stabilizer R c)).map (stabilizer R c).subtype) := by
  obtain ⟨r, s, _h, hrc, hrQ, hsc, hsQ, _hhc, _hhQ, hrne, hsne, hgen, _hhne, _hsmall⟩ :=
    SourceOrbit.source_orbit_witness common edge d c b hd hc hdb hcb C hcard hC hnot
  let Fd := Z R b ⊓ (center (stabilizer R d)).map (stabilizer R d).subtype
  let Fc := Z R b ⊓ (center (stabilizer R c)).map (stabilizer R c).subtype
  have hCF : C ≤ Fc := le_inf
    ((hC.trans inf_le_left).trans (edge.edge_commutator_le_Z d b hd hdb))
    (hC.trans inf_le_right)
  have hplane (g : FreeAmalgam R) (hgc : g ∈ stabilizer R c)
      (hgQ : g ∈ normalizer (Q R b : Set (FreeAmalgam R)))
      (hgne : ⁅Z R (act R g d), Q R b⁆ ≠ ⁅Z R d, Q R b⁆) :
      ⁅Z R (act R g d), Q R b⁆ ≤ Fd ⊔ Fc := by
    obtain ⟨_, hsplit⟩ := conjugate_plane_split_of_retained_line common initial edge d c b
      hd hdb hcentral C hcard hC g hgc hgQ hgne
    have hD := conjugate_radius_displacement_le common d b hd hdb hcentral g hgQ
    have hDF : ⁅V R d, Z R (act R g d)⁆ ≤ Fd := le_inf
      ((hD.trans inf_le_left).trans (conjugate_plane_le_edge_Z edge d b hd hdb g hgQ))
      (hD.trans inf_le_right)
    rw [← hsplit]
    exact sup_le (hCF.trans le_sup_right) (hDF.trans le_sup_left)
  apply le_antisymm
  · exact hgen.ge.trans
      (sup_le (sup_le (hplane r hrc hrQ hrne) (hplane s hsc hsQ hsne)) le_sup_right)
  · exact sup_le inf_le_left inf_le_left

end Midpoint.Source

/-- The complete source midpoint edge-plane centrality implication. The
normalizer action, conjugate escape, orbit generation, small-index choice and
symmetry are all supplied by the proved source arguments. -/
theorem critical_edge_plane_central_of_derived_central
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (initial : InitialFacts R geometry) (edge : EdgeFacts R)
    (d e c b : Vertex R) (hd : color R d = false)
    (hcrit : CriticalPair R d e (geometry.exists_critical d hd))
    (hdc : (cosetGraph R).dist d c = 2) (hce : (cosetGraph R).dist c e = 2)
    (hdb : Adjacent R d b) (hcb : Adjacent R c b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype) :
    ⁅Z R d, Q R b⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype := by
  by_contra hnot
  have hc : color R c = false :=
    (color_eq_of_dist_even R d c (by rw [hdc]; decide)).symm.trans hd
  let C := ⁅Z R d, Z R e⁆
  have hCcard : Nat.card C = 2 := Midpoint.critical_line_card common d e hd hcrit
  have hC := Midpoint.critical_line_le_edge_and_midpoint_center common hb d e c b hd
    hcrit hdc hce hcb hcentral
  obtain ⟨_r, _s, h, _hrc, _hrQ, _hsc, _hsQ, hhc, hhQ, _hrne, _hsne, _hgen, hhne, hsmall⟩ :=
    Midpoint.SourceOrbit.source_orbit_witness common edge d c b hd hc hdb hcb C hCcard hC hnot
  let D := ⁅V R d, Z R (act R h d)⁆
  let P := ⁅Z R (act R h d), Q R b⁆
  obtain ⟨hdisjoint, hsplit⟩ := Midpoint.Source.conjugate_plane_split_of_retained_line
    common initial edge d c b hd hdb hcentral C hCcard hC h hhc hhQ hhne
  have hD := Midpoint.Source.conjugate_radius_displacement_le common d b hd hdb hcentral h hhQ
  have hCn : D ≤ normalizer C := (hD.trans inf_le_right).trans
    (Midpoint.Source.embedded_center_normalizes C (stabilizer R d)
      ((hC.trans inf_le_left).trans ((edge_commutator_le_natural common d b hd hdb).trans
        ((U_le_Z d).trans (Z_le_stabilizer R d)))))
  have hPcard : Nat.card P = 4 := Midpoint.Source.conjugate_plane_card edge d b hd hdb h hhQ
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint C D hCn (disjoint_iff.mpr hdisjoint)
  have hDcard : Nat.card D = 2 := by
    rw [hsplit, hPcard, hCcard] at hprod
    omega
  have hn : ¬ P ≤ (center (stabilizer R d)).map (stabilizer R d).subtype := by
    intro hfix
    have hCP := Midpoint.Source.retained_line_le_conjugate_plane d c b C hC h hhc hhQ
    have hzero : C = ⊥ := le_bot_iff.mp
      ((le_inf (hC.trans inf_le_left) (hCP.trans hfix)).trans
        (Midpoint.edge_plane_inf_center common d b hd hdb).le)
    have hc1 := card_eq_one.mpr hzero
    omega
  obtain ⟨k, hk, hZ, _hQ, _hV, hcenter⟩ :=
    Midpoint.Source.exists_edge_actor_source_data common d b hd hdb h hhQ
  have hkb : act R k b = b := hk
  have hdb' : Adjacent R (act R k d) b := by
    simpa only [hkb] using (adjacent_act_iff R k d b).mpr hdb
  have hd' : color R (act R k d) = false := (action_preserves_color R k d).trans hd
  have hcentral' := derived_central_at_all d hd hcentral (act R k d) hd'
  have hDpair : D ≤ ⁅Z R (act R k d), Q R b⁆ ⊓
      (center (stabilizer R d)).map (stabilizer R d).subtype := by
    rwa [hZ]
  have hnot' : ¬ ⁅Z R (act R k d), Q R b⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype := by
    rwa [hZ]
  have hspan := Midpoint.Source.center_span_of_retained_line common initial edge
    (act R k d) d b hd' hd hdb' hdb hcentral' D hDcard hDpair hnot'
  rw [hcenter, sup_comm] at hspan
  exact Midpoint.not_edge_center_span_of_small_fixed_index common edge d b hd hdb h hsmall hspan

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
