module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.BadImage.Pairing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Plane
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Incident fixed points and the displacement-plane order

The actual incident displacement is a nontrivial normal subgroup of the
edge two-group. The finite two-group center theorem therefore supplies a
nonidentity point of that displacement fixed by the whole incident actor.
Fixation of V_u ∩ W modulo B_c is one sufficient way to make this point
annihilate the incident image; that fixation is left explicit.

The independent selected-parabolic plane theorem supplies order four at all
edges by edge transitivity. This uses its genuine ParabolicSeed input and
does not assume that the supplied EdgeData was constructed by that theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), pp.890–891.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a c u : Vertex R}

/-- A nonzero point in the actual incident displacement is fixed by Q_u.
No plane-fixer description or order-four assumption is needed. -/
theorem exists_incident_fixed_point (common : CommonFacts R source geometry)
    (hc : color R c = false) (hcu : Adjacent R c u) :
    ∃ w : U R c, w ≠ 1 ∧ (w : FreeAmalgam R) ∈ edgeCommutator R c u ∧
      (w : FreeAmalgam R) ∈ centralizer (Q R u : Set (FreeAmalgam R)) := by
  let E := edgeCommutator R c u
  let T := Q R u
  have hEU : E ≤ U R c := Escape.EdgeTransfer.edge_commutator_le_natural
    common.large_distance (moduleFacts common) c u hc hcu
  have hET : E ≤ T := hEU.trans ((U_le_Z R c).trans
    (Escape.EdgeTransfer.edge_Z_le_Q common.large_distance c u hc hcu))
  have hTS : T ≤ stabilizer R c := fun _ hq => hq.2 c (adjacent_symm R hcu)
  let := finite_stabilizer R c
  let : Finite T := Finite.of_injective (inclusion hTS) (inclusion_injective _)
  let : Fact (IsPGroup 2 T) := ⟨Escape.EdgeTransfer.edge_kernel_two source c u hc hcu⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr
    (Escape.EdgeTransfer.edge_commutator_ne_bot (moduleFacts common) c u hc hcu)
  let : Nontrivial (E.subgroupOf T) := (subgroupOfEquivOfLe hET).toEquiv.nontrivial
  let : (E.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_right (Z R c) (Q R u))
  obtain ⟨z, hzne, hzfix⟩ := exists_nontrivial_center_mem_normal (E.subgroupOf T) (p := 2)
  refine ⟨⟨(z : T), hEU z.property⟩, ?_, z.property, ?_⟩
  · intro hz
    apply hzne
    have hz' : ((z : T) : FreeAmalgam R) = 1 :=
      congrArg (fun w : U R c => (w : FreeAmalgam R)) hz
    exact Subtype.ext (Subtype.ext hz')
  · intro q hq
    exact congrArg Subtype.val ((mem_center_iff.mp hzfix) ⟨q,hq⟩)

/-- A literal intersection commutator bound supplies the radius pairing for
every point of the incident displacement. -/
theorem radius_annihilates_edge_of_commutator (common : CommonFacts R source geometry)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (hcu : Adjacent R c u)
    (hcomm : ⁅localZSpan R a c ⊓ V R u, Q R u⁆ ≤ B R c (geometry.Z_normal c))
    (w : U R c) (hw : (w : FreeAmalgam R) ∈ edgeCommutator R c u)
    (x : localZSpan R a c) (hx : (x : FreeAmalgam R) ∈ V R u) :
    dotProduct (naturalCoordinates f w).toAdd
      (coordinates source hc hd hb f hop x).toAdd = 0 := by
  rw [dotProduct_comm]
  apply fixed_annihilates_edge common hc hd hb f hop hcu x ?_
    (mem_map_of_mem (naturalCoordinates f).toMonoidHom hw)
  intro q hq
  rw [commutator_comm] at hcomm
  exact hcomm (commutator_mem_commutator hq ⟨x.property, hx⟩)

/-- The checked parabolic-plane deduction transports to the original edge
of any supplied EdgeData; no constructor for that EdgeData is required. -/
theorem edge_card_four_of_parabolic (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (p : ParabolicSeed geometry f) (s : EdgeData a c) :
    Nat.card (edgeCommutator R a s.neighbor) = 4 := by
  obtain ⟨_, hfour⟩ := p.displacement_plane common hb ha hc hd f hop
  have hKE := p.toMovingSeed.displacement_le_edge ha
  have hEU := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (moduleFacts common) a p.neighbor ha p.adjacent_start
  let := finite_stabilizer R a
  let : Finite (edgeCommutator R a p.neighbor) := Finite.of_injective
    (inclusion (hEU.trans ((U_le_Z R a).trans (Z_le_stabilizer R a)))) (inclusion_injective _)
  have hEfour : Nat.card (edgeCommutator R a p.neighbor) = 4 := by
    have hle := Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (moduleFacts common) a p.neighbor ha p.adjacent_start
    change Nat.card (edgeCommutator R a p.neighbor) ≤ 4 at hle
    have hge : 4 ≤ Nat.card (edgeCommutator R a p.neighbor) := hfour ▸ card_le_of_le hKE
    omega
  exact (DistanceFour.Early.OrderTwo.edge_card_eq a s.neighbor a p.neighbor
    ha ha s.adjacent_start p.adjacent_start).trans hEfour

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans.BadImage
