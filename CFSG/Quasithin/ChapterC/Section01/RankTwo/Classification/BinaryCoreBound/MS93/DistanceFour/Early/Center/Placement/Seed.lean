module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeAction

/-!
# The selected noncentral generator in (4.6.7)

The edge actor is contained in the actual vertex stabilizer. The edge
commutator bounds put the whole edge radius in its fixed preimage on V_d/Z_d.
For the selected generator, B_a acts nontrivially on Z_d, hence escapes Q_d.
Its displacement on V_d lies in Z_a and has order at most two modulo Z_d.
These are inputs to natural-module recognition, not an assumed recognition.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.7), printed p.904.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
open NaturalStructure.Exclusion
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The two endpoints of the selected edge have M-color. -/
theorem seed_color (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) : color R d = false := by
  have h₁ := adjacent_color_ne R hab
  have h₂ := adjacent_color_ne R hdb
  cases hb : color R b <;> cases hd : color R d <;> simp_all

/-- The literal actor Q_b acts on the quotient at d, without truncation. -/
theorem edge_actor_le_stabilizer (b d : Vertex R) (hdb : Adjacent R d b) :
    Q R b ≤ stabilizer R d := fun _ hx => hx.2 d (adjacent_symm R hdb)

/-- The incident edge radius is fixed modulo Z_d by all of Q_b. -/
theorem edge_radius_le_fixed (common : CommonFacts R source geometry)
    (edge : EdgeFacts R) (d b : Vertex R) (hd : color R d = false)
    (hdb : Adjacent R d b) : V R b ≤ radiusFixed geometry d (Q R b) := by
  apply radius_le_of_h_neighbors hd hdb
  intro c hcb x hx
  apply (mem_radiusFixed_iff common d hd (Q R b)
    (edge_actor_le_stabilizer b d hdb) x).mpr
  have hc := seed_color d b c hd hdb hcb
  have hcbV : Z R c ≤ V R b := le_iSup_of_le c (le_iSup_of_le
    (show (cosetGraph R).dist c b ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hcb)).le.trans
        (by decide)) le_rfl)
  refine ⟨edge_radius_le_radius hd hdb (hcbV hx), ?_⟩
  intro g hg
  have hcomm : ⁅Q R b, Z R c⁆ ≤ Z R d := by
    rw [commutator_comm]
    exact (edge.edge_commutator_le_Z c b hc hcb).trans (edge_Z_le d b hd hdb)
  exact hcomm (commutator_mem_commutator hg hx)

/-- B is normalized by its local stabilizer, using its literal covariance. -/
theorem B_normalized [Finite M] (common : CommonFacts R source geometry)
    (a : Vertex R) (ha : color R a = false) :
    stabilizer R a ≤ normalizer (B R a (geometry.Z_normal a) : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (B R a (geometry.Z_normal a)).map (MulAut.conj g).toMonoidHom = _
  have h := Escape.PairingControl.FirstPairing.B_act common.large_distance g⁻¹ a ha
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using h.symm

/-- The kernel action from (4.6.5) extends B's defining residual fixation
to the whole stabilizer, modulo Z. -/
theorem B_commutator_stabilizer_le_Z [Finite M] (common : CommonFacts R source geometry)
    (edge : EdgeFacts R) (a : Vertex R) (ha : color R a = false) :
    ⁅B R a (geometry.Z_normal a), stabilizer R a⁆ ≤ Z R a := by
  let P := commutatorPreimage (stabilizer R a) (B R a (geometry.Z_normal a)) (Z R a)
  have hL : Ltilde R a ≤ P := by
    apply le_commutatorPreimage (Ltilde_le_stabilizer a)
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff R a (geometry.Z_normal a)
      ((radius_le_Q common a ha).trans (fun _ hv => hv.1)) x).mp hx).2 l hl
  have hQ : Q R a ≤ P := by
    apply le_commutatorPreimage (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)
    rw [commutator_comm]
    exact (commutator_mono (B_le_radius common a ha) le_rfl).trans
      (edge.commutator_le_Z a ha)
  have hS : stabilizer R a ≤ P := by
    rw [← source.local_generation a ha]
    exact sup_le hL hQ
  rw [commutator_comm]
  exact (commutator_mono hS le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (Z_normalized R a))

/-- The easy direction of the source fixed-space equality. It uses the whole
edge actor and the defining residual fixed preimage, with no natural marking. -/
theorem fixed_product_le_fixed [Finite M] (common : CommonFacts R source geometry)
    (edge : EdgeFacts R) (d b : Vertex R) (hd : color R d = false)
    (hdb : Adjacent R d b) :
    (V R b ⊓ Vcirc R d) ⊔ B R d (geometry.Z_normal d) ≤
      radiusFixed geometry d (Q R b) := by
  apply sup_le (inf_le_left.trans (edge_radius_le_fixed common edge d b hd hdb))
  intro x hx
  apply (mem_radiusFixed_iff common d hd (Q R b)
    (edge_actor_le_stabilizer b d hdb) x).mpr
  refine ⟨B_le_radius common d hd hx, ?_⟩
  intro g hg
  have hcomm := B_commutator_stabilizer_le_Z common edge d hd
  rw [commutator_comm] at hcomm
  exact hcomm (commutator_mem_commutator (edge_actor_le_stabilizer b d hdb hg) hx)

/-- The neighboring radius acts inside the first endpoint stabilizer. -/
theorem neighbor_radius_le_stabilizer (hb : geometry.b R = 4)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) : V R d ≤ stabilizer R a := by
  have hd := seed_color a b d ha hab hdb
  have had : (cosetGraph R).dist a d ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hab)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdb))
    have htri := (cosetGraph_connected R).dist_triangle (u := a) (v := b) (w := d)
    omega
  apply Initial.radius_le_of_generators d hd
  intro c hc hcd
  exact geometry.ball_Z_le_stabilizer (by omega) d c a hc hcd had

/-- The first displacement assertion after the choice of delta on p.904. -/
theorem seed_commutator_le_Z [Finite M] (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) :
    ⁅B R a (geometry.Z_normal a), V R d⁆ ≤ Z R a :=
  (commutator_mono le_rfl (neighbor_radius_le_stabilizer hb a b d ha hab hdb)).trans
    (B_commutator_stabilizer_le_Z common edge a ha)

/-- Noncentrality of the selected generator is nontriviality of the
actual actor image in the neighboring local quotient. -/
theorem seed_not_le_kernel (geometry : Geometry R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hseed : ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥) :
    ¬ B R a (geometry.Z_normal a) ≤ Q R d := by
  intro h
  apply hseed
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact h.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (geometry.centralizes d (seed_color a b d ha hab hdb))))

/-- The source seed has at most one binary displacement dimension modulo Z_d.
Both Z-layers contain Z_b, whose index in Z_a is two. -/
theorem seed_displacement_index_le_two [Finite M] (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) :
    (Z R d).relIndex (⁅B R a (geometry.Z_normal a), V R d⁆) ≤ 2 := by
  let := finite_radius common a ha
  let : Finite (Z R a) := Finite.of_injective
    (inclusion (show Z R a ≤ V R a from Z_le_VBall R a 2))
    (inclusion_injective _)
  have hd := seed_color a b d ha hab hdb
  calc
    (Z R d).relIndex (⁅B R a (geometry.Z_normal a), V R d⁆) ≤
        (Z R d).relIndex (Z R a) := relIndex_le_of_le_right
      (seed_commutator_le_Z common hb edge a b d ha hab hdb) index_ne_zero_of_finite
    _ ≤ (Z R b).relIndex (Z R a) := relIndex_le_of_le_left
      (edge_Z_le d b hd hdb) index_ne_zero_of_finite
    _ = 2 := edge.edge_Z_index a b ha hab

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
