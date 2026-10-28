module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.FixedQuotient

/-!
# Edge placement from the fixed quotient

The incident edge radius lies in the fixed preimage on V_d/Z_d. A cover of
that preimage by (V_b intersect Vcirc_d) B_d, together with the fixed/moving
intersection bound, places B_d in V_b. The proof factors elements twice in
normalized subgroup products. All normalization is relative to the local
stabilizer, never the infinite free amalgam.

The imported calculation proves the natural-section recognition, the source
cover Z_a ≤ Vcirc_d Z_d, and the literal fixed-preimage equality for Q_b.
The final theorem discharges both premises of the group-theoretic reduction
and supplies the selected edge placement used by the center argument.
Selection of the seed and the final center contradiction belong to the parent
assembly of (4.6.7).
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.7), printed p.904.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
open NaturalStructure.Exclusion

private theorem placement_of_fixed_cover {G : Type*} [Group G]
    (P W C : Subgroup G)
    (hWP : W ≤ normalizer (P : Set G))
    (hWC : W ≤ normalizer (C : Set G))
    (hC : C ≤ P ⊔ W) (hI : P ⊓ C ≤ W)
    (hfixed : W ≤ (W ⊓ P) ⊔ C) : C ≤ W := by
  intro c hc
  have hprod : c ∈ (P : Set G) * (W : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left P W hWP]
    exact hC hc
  obtain ⟨p, hp, w, hw, rfl⟩ := hprod
  have hprod' : w ∈ ((W ⊓ P : Subgroup G) : Set G) * (C : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right (W ⊓ P) C (inf_le_left.trans hWC)]
    exact hfixed hw
  obtain ⟨i, ⟨hiW, hiP⟩, z, hzC, rfl⟩ := hprod'
  have hzW : z ∈ W := by
    simpa only [inv_mul_cancel_left] using W.mul_mem (W.inv_mem hiW) hw
  have hpiC : p * i ∈ C := by
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using C.mul_mem hc (C.inv_mem hzC)
  have hpiW := hI ⟨P.mul_mem hp hiP, hpiC⟩
  simpa only [mul_assoc] using W.mul_mem hpiW hzW


variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The group-theoretic conclusion of the source fixed-quotient calculation,
isolating the fixed-preimage bound and fixed/moving intersection. -/
theorem edge_placement_of_fixed_quotient (common : CommonFacts R source geometry)
    (edge : EdgeFacts R) (d b : Vertex R) (hd : color R d = false)
    (hdb : Adjacent R d b)
    (hfixed : radiusFixed geometry d (Q R b) ≤
      (V R b ⊓ Vcirc R d) ⊔ B R d (geometry.Z_normal d))
    (hinter : Vcirc R d ⊓ B R d (geometry.Z_normal d) ≤ Z R d) :
    B R d (geometry.Z_normal d) ≤ V R b := by
  have hWS : V R b ≤ stabilizer R d :=
    (edge_radius_le_radius hd hdb).trans
      ((radius_le_Q common d hd).trans (fun _ hx => hx.1))
  have hZW : Z R d ≤ V R b := le_iSup_of_le d (le_iSup_of_le
    (show (cosetGraph R).dist d b ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdb)).le.trans
        (by decide)) le_rfl)
  apply placement_of_fixed_cover (Vcirc R d) (V R b) (B R d (geometry.Z_normal d))
    (hWS.trans (Vcirc_normalized d)) (hWS.trans (Placement.B_normalized common d hd))
  · rw [← radius_eq_moving_sup_edge source hd hdb]
    exact B_le_radius common d hd
  · exact hinter.trans hZW
  · exact (Placement.edge_radius_le_fixed common edge d b hd hdb).trans hfixed

/-- At the selected noncentral generator, the fixed-space upper bound is the
only remaining input to edge placement. Natural recognition and the
fixed/moving intersection are discharged here. -/
theorem edge_placement_of_seed_fixed_quotient (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hseed : ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥)
    (hfixed : radiusFixed geometry d (Q R b) ≤
      (V R b ⊓ Vcirc R d) ⊔ B R d (geometry.Z_normal d)) :
    B R d (geometry.Z_normal d) ≤ V R b :=
  edge_placement_of_fixed_quotient common edge d b
    (Placement.seed_color a b d ha hab hdb) hdb hfixed
    (Placement.seed_moving_fixed_intersection_le_Z common hb edge a b d ha hab hdb hseed)

/-- The selected edge placement in MS93 (4.6.7), with the constituent and
fixed-quotient calculations discharged. The initial facts, global noncentrality,
and center failure are retained for the parent assembly's exact interface;
their role in selecting the noncentral seed has already been fulfilled. -/
theorem edge_placement_of_noncentral_seed (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (_initial : InitialFacts R geometry) (edge : EdgeFacts R)
    (_noncentral : ∀ c, color R c = false →
      ¬ ⁅V R c, V R c⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (_hfail : ¬ B R a (geometry.Z_normal a) ≤ (center (V R a)).map (V R a).subtype)
    (hseed : ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥) :
    B R d (geometry.Z_normal d) ≤ V R b :=
  edge_placement_of_seed_fixed_quotient common hb edge a b d ha hab hdb hseed
    (Placement.seed_fixed_quotient common hb edge a b d ha hab hdb hseed).le

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
