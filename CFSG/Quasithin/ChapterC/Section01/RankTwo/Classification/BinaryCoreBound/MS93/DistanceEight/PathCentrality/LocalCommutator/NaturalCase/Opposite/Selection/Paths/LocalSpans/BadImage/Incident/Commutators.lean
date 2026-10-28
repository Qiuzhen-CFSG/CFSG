module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.BadImage.Geometry
public import Theory.GroupTheory.PGroup.SmallElementaryNormal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry

/-!
# Commutators of the incident radius

The displacement [Z_c,Q_u] has order at most four and is normal in the
finite two-group Q_u. Its next commutator is central in Q_u, hence lies
in Z_u by the actual edge fixed-point identity. Neighbor generation and
commutator preimages extend this to [[V_u,Q_u],Q_u] ≤ Z_u.

If one incident displacement already lies in Z_u, edge transitivity
propagates that containment to every neighbor and gives [V_u,Q_u] ≤ Z_u.
These bounds feed the marked-duality argument in Incident.Properness.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), pp.890–891,
the incident-radius factor in the bad-conjugate display.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a c u : Vertex R}

/-- The second incident-edge commutator lies in the center seed at u. -/
theorem edge_second_commutator_le (common : CommonFacts R source geometry)
    (hc : color R c = false) (hcu : Adjacent R c u) :
    ⁅⁅Z R c, Q R u⁆, Q R u⁆ ≤ Z R u := by
  let E := ⁅Z R c, Q R u⁆
  let T := Q R u
  have hEU : E ≤ U R c := Escape.EdgeTransfer.edge_commutator_le_natural
    common.large_distance (moduleFacts common) c u hc hcu
  have hEZ : E ≤ Z R c := hEU.trans (U_le_Z R c)
  have hZT : Z R c ≤ T := Escape.EdgeTransfer.edge_Z_le_Q
    common.large_distance c u hc hcu
  have hET : E ≤ T := hEZ.trans hZT
  let := finite_stabilizer R u
  let : Finite T := Finite.of_injective
    (inclusion (show Q R u ≤ stabilizer R u from fun _ h => h.1)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (Z R c) :=
    geometry.Z_elementary (by have h := common.large_distance; omega) c hc
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le hEZ
  let : IsElementaryAbelian 2 (E.subgroupOf T) := IsElementaryAbelian.subgroupOf hET
  let : (E.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_right (Z R c) (Q R u))
  have hcard : Nat.card (E.subgroupOf T) ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv]
    exact Escape.EdgeTransfer.edge_displacement_card_le_four
      common.large_distance (moduleFacts common) c u hc hcu
  have hcen := commutator_le_center_of_elementary_card_le_four
    (Escape.EdgeTransfer.edge_kernel_two source c u hc hcu) (E.subgroupOf T) hcard
  have hcentral : ⁅E,T⁆ ≤ centralizer (T : Set (FreeAmalgam R)) := by
    have hm := Subgroup.map_mono (f := T.subtype) hcen
    rw [map_commutator, map_subgroupOf_eq_of_le hET,
      ← MonoidHom.range_eq_map, range_subtype] at hm
    rintro x hx t ht
    obtain ⟨y, hy, rfl⟩ := hm hx
    exact congrArg Subtype.val ((mem_center_iff.mp hy) ⟨t,ht⟩)
  rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
    (moduleFacts common) c u hc hcu]
  exact le_inf ((commutator_mono hEZ le_rfl).trans hEZ) hcentral

/-- The actual radius satisfies the same second-commutator bound as its
neighbor generators. -/
theorem radius_second_commutator_le (common : CommonFacts R source geometry)
    (hc : color R c = false) (hcu : Adjacent R c u) :
    ⁅⁅V R u, Q R u⁆, Q R u⁆ ≤ Z R u := by
  let T := Q R u
  let N := Z R u
  have hTZ : T ≤ normalizer (N : Set (FreeAmalgam R)) :=
    (show Q R u ≤ stabilizer R u from fun _ h => h.1).trans (Z_normalized R u)
  have hNT : N ≤ T := (Escape.EdgeTransfer.edge_Z_le c u hc hcu).trans
    (Escape.EdgeTransfer.edge_Z_le_Q common.large_distance c u hc hcu)
  let K := commutatorPreimage T T N
  have hNK : N ≤ K := le_commutatorPreimage hNT
    (le_normalizer_iff_commutator_le_left.mp hTZ)
  have hTK : T ≤ normalizer (K : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_commutatorPreimage_le T T N hTZ).trans hNK)
  have hV : V R u ≤ commutatorPreimage T T K := by
    apply Escape.Initial.Consequences.V_le_of_h_neighbors hc hcu
    intro d hdu
    have hd : color R d = false := by
      have hne := adjacent_color_ne R hdu
      have hne' := adjacent_color_ne R hcu
      cases he : color R d <;> cases he' : color R u <;> simp_all
    have hZd : Z R d ≤ T := Escape.EdgeTransfer.edge_Z_le_Q
      common.large_distance d u hd hdu
    apply le_commutatorPreimage hZd
    apply le_commutatorPreimage ((commutator_mono hZd le_rfl).trans (commutator_le_self T))
    exact edge_second_commutator_le common hd hdu
  exact ((commutator_mono ((commutator_mono hV le_rfl).trans
    (commutator_commutatorPreimage_le T T K hTK)) le_rfl).trans
    (commutator_commutatorPreimage_le T T N hTZ))

omit [Finite M] in
/-- Edge transitivity upgrades one edge containment to a radius bound. -/
theorem radius_commutator_le_of_edge_le (common : CommonFacts R source geometry)
    (hc : color R c = false) (hcu : Adjacent R c u)
    (hE : ⁅Z R c,Q R u⁆ ≤ Z R u) :
    ⁅V R u, Q R u⁆ ≤ Z R u := by
  let T := Q R u
  have hTZ : T ≤ normalizer (Z R u : Set (FreeAmalgam R)) :=
    (show Q R u ≤ stabilizer R u from fun _ h => h.1).trans (Z_normalized R u)
  have hV : V R u ≤ commutatorPreimage T T (Z R u) := by
    apply Escape.Initial.Consequences.V_le_of_h_neighbors hc hcu
    intro d hdu
    have hd : color R d = false := by
      have hne := adjacent_color_ne R hdu
      have hne' := adjacent_color_ne R hcu
      cases he : color R d <;> cases he' : color R u <;> simp_all
    apply le_commutatorPreimage (Escape.EdgeTransfer.edge_Z_le_Q
      common.large_distance d u hd hdu)
    change ⁅Z R d, Q R u⁆ ≤ Z R u
    obtain ⟨g, hg | hg⟩ := edge_transitive R hcu hdu
    · rw [← hg.1, ← hg.2, Z_act, Q_act, ← map_commutator, Z_act]
      exact map_mono hE
    · have hcol : color R u = false := by
        rw [← hg.1, action_preserves_color]
        exact hc
      exact (adjacent_color_ne R hdu (hd.trans hcol.symm)).elim
  exact (commutator_mono hV le_rfl).trans
    (commutator_commutatorPreimage_le T T (Z R u) hTZ)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
