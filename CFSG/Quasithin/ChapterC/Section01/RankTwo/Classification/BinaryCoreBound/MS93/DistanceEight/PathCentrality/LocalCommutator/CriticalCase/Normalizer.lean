module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.RadiusGrowth

/-!
# Normalizer inputs on the actual backward critical path

Reversing the constructed critical replacement and using distance-two
minimality discharges the geometric hypotheses of (2.1)(vi). Failure of
normalization then gives precisely the ordered triple-commutator
noncontainment used on p.892.

At any critical path, the endpoint Z-layer normally generates the starting
stabilizer modulo its kernel: this uses critical reversal and the genuine
simple SL3(2) quotient. Enlarging the kernel to any incident edge gives the
generation premise in (2.1)(vii). Relative normality and nonnormality of the
two subgroups used in the terminal selections are still to be proved.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.1)(vi--vii), pp.855--856, applied in (4.4.1), p.892.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

/-- The source-ordered noncontainment from (2.1)(vi), with all geometric premises discharged. -/
theorem commutator_not_le_triple_sup [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (w : BackwardWitness R geometry a c) {lam : Vertex R}
    (hlam : (cosetGraph R).dist w.predecessor lam = 2)
    (hn : ¬ Z R w.backward ≤ normalizer
      (⁅Z R lam, Q R w.predecessor⁆ ⊔ Z R w.predecessor : Subgroup (FreeAmalgam R))) :
    ¬ ⁅Z R lam, Z R w.backward⁆ ≤
      ⁅⁅Z R lam, Q R w.predecessor⁆, Z R w.backward⁆ ⊔ Z R w.predecessor := by
  have hcol : color R lam = false :=
    (color_eq_of_dist_even R lam w.predecessor (by
      rw [SimpleGraph.dist_comm, hlam]; decide)).trans w.predecessor_color
  have hZQ : Z R lam ≤ Q R w.predecessor := by
    apply Z_le_Q_of_dist_lt R lam (geometry.exists_critical lam hcol)
    rw [geometry.distance_constant lam hcol, SimpleGraph.dist_comm, hlam]
    exact lt_trans (by decide : 2 < 4) hb
  have hpos : 0 < criticalDistance R w.predecessor
      (geometry.exists_critical w.predecessor w.predecessor_color) := by
    rw [geometry.distance_constant w.predecessor w.predecessor_color]
    change 0 < geometry.b R
    omega
  intro h
  exact hn (source_2_1_vi R source geometry w.predecessor w.predecessor_color hpos
    ((w.shifted ha (by omega)).reverse common).critical lam hlam hZQ h).2

/-- The generation premise of (2.1)(vii) at any incident edge of a genuine critical path. -/
theorem critical_conjugates_sup_edge [Finite M]
    (common : CommonFacts R source geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') {t : Vertex R} (hat : Adjacent R a t) :
    NormalizerTransfer.conjugatesIn (Z R a') (stabilizer R a) ⊔ Q R t =
      stabilizer R a := by
  have hb : 0 < geometry.b R := by have := common.large_distance; omega
  have hZA := p.endpoint_Z_le_start_stabilizer hb
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases hc : color R t <;> simp_all [p.start_color]
  have hQA : Q R t ≤ stabilizer R a := by
    rw [Q_h_eq_edge R ht hat]
    exact inf_le_left
  apply le_antisymm
  · exact sup_le (NormalizerTransfer.conjugatesIn_le _ _ hZA) hQA
  · calc
      stabilizer R a = NormalizerTransfer.conjugatesIn (Z R a') (stabilizer R a) ⊔
          Q R a := (Escape.Initial.local_conjugate_generation source a p.start_color
            (Z R a') hZA (p.reverse common).critical.2).symm
      _ ≤ _ := sup_le_sup_left (Q_le_adjacent_h R ht hat) _

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
