module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Path
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Moving

/-!
# Generation and independence for the second higher orbit layer

`DeltaChoice` records the source selection delta in the G_c orbit of a with
hat V_c = Z_a Z_delta Z_d. It does not assert that such a vertex exists.
`orbitFactor` includes the common denominator explicitly, so no containment
in a single orbit span is silently assumed.

The selected equality generates hat W_a by the two actual orbit factors.
The first lies in Q_d by (4.5.4)(ii) and the radius-six bound. In contrast,
the literal product (4.5.1)(iv) and the preceding edge index four force
hat W_a outside Q_d. Thus the second factor is not contained in the first,
independently of any quotient recognition.

Selection of delta and recognition of both single factors remain source
obligations. The conditional marked-pair consumer is in `SecondLayer`.
The product premise is produced by the early-layer owner; orbit containment
is produced by the higher orbit-geometry owner.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)(iv), p.896, and the
proof of (4.5.4)(iii), p.899.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer
open NormalizerTransfer
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The source-selected delta on p.899. Selection is an obligation; the
record retains its actual transporter and three generating Z subgroups. -/
structure DeltaChoice (p : Higher.SourcePath (alpha R)) where
  vertex : Vertex R
  transporter : stabilizer R (p.walk.getVert 6)
  vertex_eq : vertex = act R transporter (alpha R)
  generation : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
    Z R (alpha R) ⊔ Z R vertex ⊔ Z R (p.walk.getVert 8)

/-- One orbit factor, with the common denominator included explicitly. -/
noncomputable def orbitFactor (p : Higher.SourcePath (alpha R)) (v : Vertex R) :
    Subgroup (FreeAmalgam R) :=
  conjugatesIn (Z R v) (stabilizer R (alpha R)) ⊔
    hatV R (alpha R) (p.walk.getVert 6)

private theorem seed_le_span {G : Type*} [Group G] (A P : Subgroup G) :
    A ≤ conjugatesIn A P := by
  intro x hx
  apply (le_iSup (fun g : P => rightConjugate A g) 1)
  exact ⟨x, hx, by simp⟩

private theorem span_le {G : Type*} [Group G] {A P B : Subgroup G}
    (hA : A ≤ B) (hB : P ≤ normalizer B) : conjugatesIn A P ≤ B := by
  apply iSup_le
  intro g
  exact (map_mono hA).trans
    (mem_normalizer_iff_map_conj_eq.mp (hB (P.inv_mem g.property))).le

private theorem normalized_join {G : Type*} [Group G] {A B P : Subgroup G}
    (hA : P ≤ normalizer A) (hB : P ≤ normalizer B) :
    P ≤ normalizer (A ⊔ B : Subgroup G) :=
  (le_inf hA hB).trans (normalizer_inf_normalizer_le_normalizer_sup A B)

private theorem path_color (p : Higher.SourcePath (alpha R))
    {i : ℕ} (hi : Even i) (hle : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; exact hle)).mpr hi

/-- The first layer lies in the second layer, using the actual common edge. -/
theorem lower_le_second [Finite M] (p : Higher.SourcePath (alpha R)) :
    hatV R (alpha R) (p.walk.getVert 6) ≤
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
  rw [hatV_eq_conjugatesIn]
  apply span_le _ (hatW_normalized R _ _ _)
  exact (Early.Z_le_hatV (path_color p (by decide) (by decide))
    (p.dist (i := 6) (j := 8) (by decide) (by decide))).trans
      (seed_le_span _ _)

/-- A selected delta generates the second layer by the two stated orbit
factors. This distributes the actual relative conjugate span, not a label. -/
theorem DeltaChoice.factors_generate [Finite M]
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p) :
    orbitFactor p (p.walk.getVert 8) ⊔ orbitFactor p δ.vertex =
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
  let A := conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R))
  let B := conjugatesIn (Z R δ.vertex) (stabilizer R (alpha R))
  let N := hatV R (alpha R) (p.walk.getVert 6)
  let H := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  have hN : N ≤ H := lower_le_second p
  have hA : A ≤ H := by
    apply span_le _ (hatW_normalized R _ _ _)
    exact ((show Z R (p.walk.getVert 8) ≤
      Z R (alpha R) ⊔ Z R δ.vertex ⊔ Z R (p.walk.getVert 8) from le_sup_right).trans
        δ.generation.ge).trans (seed_le_span _ _)
  have hB : B ≤ H := by
    apply span_le _ (hatW_normalized R _ _ _)
    exact ((show Z R δ.vertex ≤
      Z R (alpha R) ⊔ Z R δ.vertex ⊔ Z R (p.walk.getVert 8) from
        le_sup_right.trans le_sup_left).trans δ.generation.ge).trans (seed_le_span _ _)
  have hn : stabilizer R (alpha R) ≤ normalizer ((A ⊔ N) ⊔ (B ⊔ N) : Subgroup (FreeAmalgam R)) :=
    normalized_join
      (normalized_join (conjugatesIn_normalized _ _) (hatV_normalized R _ _))
      (normalized_join (conjugatesIn_normalized _ _) (hatV_normalized R _ _))
  change (A ⊔ N) ⊔ (B ⊔ N) = H
  apply le_antisymm (sup_le (sup_le hA hN) (sup_le hB hN))
  apply span_le _ hn
  rw [δ.generation]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (Early.Z_le_hatV (R := R) rfl
      (by simpa only [p.center_eq] using p.dist (i := 4) (j := 6) (by decide) (by decide))).trans
        (le_sup_right.trans le_sup_left)
  · exact (seed_le_span _ _).trans (le_sup_left.trans le_sup_right)
  · exact (seed_le_span _ _).trans (le_sup_left.trans le_sup_left)

/-- The first factor lies in Q_d: orbit containment is exactly (4.5.4)(ii),
and the denominator lies there by the radius-six bound. -/
theorem first_factor_le_Q {geometry : Geometry R} (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R))
    (horbit : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8)) : orbitFactor p (p.walk.getVert 8) ≤ Q R (p.walk.getVert 8) := by
  refine sup_le horbit ?_
  have had : (cosetGraph R).dist (alpha R) (p.walk.getVert 8) = 4 := by
    simpa only [p.center_eq] using p.dist (i := 4) (j := 8) (by decide) (by decide)
  exact (hatV_le_radius R p.two_step_distances.1.le).trans
    ((Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le
      (p.walk.getVert 8) (alpha R) 2 6 (by rw [had])).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q _ (path_color p (by decide) (by decide)) 6
        (by rw [earlier.distance]; decide)))

/-- The literal product (4.5.1)(iv) and |Q_t:Q_d|=4 exclude containment
of the whole second layer in Q_d. No quotient dimension is assumed. -/
theorem second_not_le_Q {geometry : Geometry R} (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R))
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R))) :
    ¬ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ≤ Q R (p.walk.getVert 8) := by
  intro h
  have hQt : Q R (p.walk.getVert 7) ≤ Q R (p.walk.getVert 8) := by
    intro x hx
    change x ∈ (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)) at hx
    rw [← hprod] at hx
    obtain ⟨w, hw, q, hq, rfl⟩ := hx
    exact (Q R (p.walk.getVert 8)).mul_mem (h hw) hq
  have hadj : Adjacent R (p.walk.getVert 8) (p.walk.getVert 7) := by
    apply adjacent_symm
    exact (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 7) (j := 8) (by decide) (by decide)))
  have hc := earlier.edge_Q_index _ _ (path_color p (by decide) (by decide)) hadj
  have hone := relIndex_eq_one.mpr hQt
  omega

/-- The selected second orbit is not contained in the first. This geometric
noncontainment is proved independently of quotient recognition. -/
theorem DeltaChoice.second_factor_not_le_first [Finite M]
    {geometry : Geometry R} (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (horbit : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8))
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R))) :
    ¬ orbitFactor p δ.vertex ≤ orbitFactor p (p.walk.getVert 8) := by
  intro h
  apply second_not_le_Q earlier p hprod
  rw [← δ.factors_generate, sup_eq_left.mpr h]
  exact first_factor_le_Q earlier p horbit

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer
