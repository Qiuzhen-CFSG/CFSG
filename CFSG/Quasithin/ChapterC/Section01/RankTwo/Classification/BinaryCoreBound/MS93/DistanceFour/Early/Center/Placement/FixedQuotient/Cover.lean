module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.Natural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Geometry
/-!
# The source cover at the selected generator

The seed B_a escapes Q_d. If its displacement on V_d were contained in Z_d,
normality of the quotient-action kernel and the simple local quotient would
make the residual fix V_d/Z_d. The amalgam obstruction excludes this.
Its nonzero displacement lies both in Z_a and in Vcirc_d Z_d. Since Z_b has
index two in Z_a and lies in Z_d, these subgroups cover all of Z_a.

All normality is relative to the finite vertex stabilizer. This proves the
cover in MS93 (4.6.7), printed p.904, without assuming the later fixed-space
calculation or the radius-center equality.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
open NaturalStructure.Exclusion
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The full stabilizer has the same moving image modulo Z as the residual. -/
theorem radius_commutator_stabilizer_le (_common : CommonFacts R source geometry)
    (edge : EdgeFacts R) (d : Vertex R) (hd : color R d = false) :
    ⁅V R d, stabilizer R d⁆ ≤ Vcirc R d ⊔ Z R d := by
  let K := Vcirc R d ⊔ Z R d
  have hn : stabilizer R d ≤ normalizer (K : Set (FreeAmalgam R)) :=
    (le_inf (Vcirc_normalized d) (Z_normalized R d)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hs : stabilizer R d ≤ commutatorPreimage (stabilizer R d) (V R d) K := by
    conv_lhs => rw [← source.local_generation d hd]
    apply sup_le
    · apply le_commutatorPreimage (Ltilde_le_stabilizer d)
      rw [commutator_comm]
      exact le_sup_left
    · apply le_commutatorPreimage (show Q R d ≤ stabilizer R d from fun _ hx => hx.1)
      rw [commutator_comm]
      exact (edge.commutator_le_Z d hd).trans le_sup_right
  rw [commutator_comm]
  exact (commutator_mono hs le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hn)

/-- An actor outside the local kernel moves the genuine radius quotient. -/
theorem radius_commutator_not_le_Z (common : CommonFacts R source geometry)
    (d : Vertex R) (hd : color R d = false) (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R d) (hout : ¬ A ≤ Q R d) :
    ¬ ⁅A, V R d⁆ ≤ Z R d := by
  intro h
  let P := commutatorPreimage (stabilizer R d) (V R d) (Z R d)
  have hP : P ≤ stabilizer R d := commutatorPreimage_le _ _ _
  have hn : (P.subgroupOf (stabilizer R d)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (commutatorPreimage_normalized _ _ _ _ (Z_normalized R d)
        (stabilizer R d).le_normalizer (V_normalized d) (Z_normalized R d))
  have hAP : A ≤ P := le_commutatorPreimage hA h
  have hLP := residual_le_of_normal_not_le source d hd P hP hn
    (fun hh => hout (hAP.trans hh))
  apply Escape.Initial.Natural.Splitting.radius_moving_not_le_Z
    source geometry common.large_distance (Initial.moduleFacts common) d hd
  rw [Vcirc, commutator_comm]
  exact (commutator_mono hLP le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (Z_normalized R d))

private theorem le_of_index_two {G : Type*} [Group G] (N H K D : Subgroup G)
    (hi : N.relIndex H = 2) (hNK : N ≤ K) (hDH : D ≤ H) (hDK : D ≤ K)
    (hout : ¬ D ≤ N) : H ≤ K := by
  obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hout
  intro y hy
  by_cases hyn : y ∈ N
  · exact hNK hyn
  have hi' : (N.subgroupOf H).index = 2 := hi
  have hm : (⟨y, hy⟩ : H) * ⟨x, hDH hx⟩ ∈ N.subgroupOf H :=
    (mul_mem_iff_of_index_two hi').mpr (iff_of_false hyn hxn)
  have hmul : y * x ∈ K := hNK hm
  simpa only [mul_inv_cancel_right] using K.mul_mem hmul (K.inv_mem (hDK hx))

/-- The source cover obtained from the selected noncentral generator. -/
theorem seed_Z_le_moving_sup_Z (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hseed : ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥) :
    Z R a ≤ Vcirc R d ⊔ Z R d := by
  have hd := seed_color a b d ha hab hdb
  have hcolb : color R b = true := by
    have hn := adjacent_color_ne R hab
    cases hc : color R b <;> simp_all
  have hBaS : B R a (geometry.Z_normal a) ≤ stabilizer R d :=
    (B_le_radius common a ha).trans ((radius_le_Q common a ha).trans
      ((Q_le_adjacent_h R hcolb hab).trans (edge_actor_le_stabilizer b d hdb)))
  have hout := radius_commutator_not_le_Z common d hd
    (B R a (geometry.Z_normal a)) hBaS
    (seed_not_le_kernel geometry a b d ha hab hdb hseed)
  apply le_of_index_two (Z R b) (Z R a) (Vcirc R d ⊔ Z R d)
    ⁅B R a (geometry.Z_normal a), V R d⁆ (edge.edge_Z_index a b ha hab)
    ((edge_Z_le d b hd hdb).trans le_sup_right)
    (seed_commutator_le_Z common hb edge a b d ha hab hdb)
  · rw [commutator_comm]
    exact (commutator_mono le_rfl hBaS).trans
      (radius_commutator_stabilizer_le common edge d hd)
  · exact fun h => hout (h.trans (edge_Z_le d b hd hdb))
/-- The seed contributes a nonzero vector of the moving quotient inside the
actual incident edge radius. This is the nonzero input for the normalizer orbit. -/
theorem seed_edge_moving_not_le_Z (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hseed : ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥) :
    ¬ V R b ⊓ (Vcirc R d ⊔ Z R d) ≤ Z R d := by
  have hd := seed_color a b d ha hab hdb
  have hcolb : color R b = true := by
    have hn := adjacent_color_ne R hab
    cases hc : color R b <;> simp_all
  have hBaS : B R a (geometry.Z_normal a) ≤ stabilizer R d :=
    (B_le_radius common a ha).trans ((radius_le_Q common a ha).trans
      ((Q_le_adjacent_h R hcolb hab).trans (edge_actor_le_stabilizer b d hdb)))
  have hout := radius_commutator_not_le_Z common d hd
    (B R a (geometry.Z_normal a)) hBaS
    (seed_not_le_kernel geometry a b d ha hab hdb hseed)
  have hZaV : Z R a ≤ V R b := le_iSup_of_le a (le_iSup_of_le
    (show (cosetGraph R).dist a b ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hab)).le.trans
        (by decide)) le_rfl)
  intro h
  exact hout ((seed_commutator_le_Z common hb edge a b d ha hab hdb).trans
    ((le_inf hZaV (seed_Z_le_moving_sup_Z common hb edge a b d ha hab hdb hseed)).trans h))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
