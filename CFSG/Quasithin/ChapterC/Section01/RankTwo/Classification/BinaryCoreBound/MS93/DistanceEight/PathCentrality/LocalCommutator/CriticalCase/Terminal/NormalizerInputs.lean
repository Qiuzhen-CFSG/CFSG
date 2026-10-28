module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inequality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Normalizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization

/-!
# Z-product normalizer premises for the terminal selections

The backward witness retains the second vertex of its shifted critical path.
Applying source (2.2)(iv--v) there proves nonnormality of the two orientations
of the Z-product in their respective local stabilizers. The escape premise
in (v) is supplied by the given common facts. The product is also contained
in, and relatively normal in, the kernel of any common odd neighbor.

These are premises for the two uses of (2.1)(vii) on p.892. The other selected
subgroups are the edge-fixed parts of the natural layers; their normalizer
premises and the terminal contradiction are separate obligations.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.2)(iv--v), printed pp.856--857, and (4.4.1), printed p.892.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

/-- The original center is exactly the second vertex of the shifted critical path. -/
theorem BackwardWitness.shifted_second {a c : Vertex R}
    (w : BackwardWitness R geometry a c) (ha : color R a = false)
    (hb : 2 ≤ geometry.b R) : (w.shifted ha hb).walk.getVert 2 = c := by
  simpa only [Nat.zero_add, SimpleGraph.Walk.getVert_zero] using
    w.shifted_overlap ha hb (i := 0) (Nat.zero_le _)

/-- The whole Z-product in the first terminal selection belongs to the edge
kernel, and is normal in that kernel, for any common neighbor. -/
theorem two_step_join_edge_normal [Finite M] (hb : 2 < geometry.b R)
    {a c t : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t) :
    Z R a ⊔ Z R c ≤ Q R t ∧
      ((Z R a ⊔ Z R c).subgroupOf (Q R t)).Normal := by
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have za (x : Vertex R) (hx : color R x = false) (hxt : Adjacent R x t) :
      Z R x ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R x (geometry.exists_critical x hx)
    rw [geometry.distance_constant x hx]
    have hd := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hxt)
    rw [hd]
    exact lt_trans (by decide : 1 < 2) hb
  have hta : Q R t ≤ stabilizer R a := by
    rw [Q_h_eq_edge R ht hat]
    exact inf_le_left
  have htc : Q R t ≤ stabilizer R c := by
    rw [Q_h_eq_edge R ht hct]
    exact inf_le_left
  refine ⟨sup_le (za a ha hat) (za c hc hct), ?_⟩
  apply normal_subgroupOf_of_le_normalizer
  exact (le_inf (hta.trans (Z_normalized R a)) (htc.trans (Z_normalized R c))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Both orientations of the backward Z-product are nonnormal in their
respective centers. These are the actual (2.2)(iv--v) inputs for the two
uses of (2.1)(vii), with the universal escape premise supplied by common. -/
theorem backward_join_nonnormal [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c) :
    (Z R w.backward ⊔ Z R c ≤ stabilizer R c ∧
      ¬ ((Z R w.backward ⊔ Z R c).subgroupOf (stabilizer R c)).Normal) ∧
    (Z R c ⊔ Z R w.backward ≤ stabilizer R w.backward ∧
      ¬ ((Z R c ⊔ Z R w.backward).subgroupOf (stabilizer R w.backward)).Normal) := by
  let p := w.shifted ha (by omega : 2 ≤ geometry.b R)
  have hp : 0 < criticalDistance R w.backward
      (geometry.exists_critical w.backward p.start_color) := by
    rw [geometry.distance_constant w.backward p.start_color]
    change 0 < geometry.b R
    omega
  have hc : (cosetGraph R).dist c w.predecessor + 2 =
      (cosetGraph R).dist w.backward w.predecessor := by
    have hs : p.walk.getVert 2 = c := w.shifted_second ha (by omega)
    have hh := p.dist_end 2
    rw [hs, p.length_eq_b] at hh
    have hh' := p.shortest.symm.trans p.length_eq_b
    omega
  have hC : EdgeCentralizerCondition R := common.centralizer
  have hforward := critical_nonnormal_forward R geometry hC w.backward
    p.start_color hp w.predecessor p.critical c (w.backward_distance hd) hc
  have hreverse := critical_nonnormal_reverse R geometry hC common.escape w.backward
    p.start_color hp p.critical c (w.backward_distance hd) hc
  simpa only [common.X_eq_Z c w.path.start_color,
    common.X_eq_Z w.backward p.start_color] using And.intro hforward hreverse

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
