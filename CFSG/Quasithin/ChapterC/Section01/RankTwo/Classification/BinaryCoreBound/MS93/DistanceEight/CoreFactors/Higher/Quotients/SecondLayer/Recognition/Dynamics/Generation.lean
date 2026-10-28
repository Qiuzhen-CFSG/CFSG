module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Dynamics.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.First

/-!
# Moving generation from an actual seed actor

For either source seed, the common denominator has relative index at most
two in its Z-layer. For delta this follows by transporting the original
edge at index five, using delta's given transporter. If an actor in G_a
moves the orbit factor outside the denominator, and its commutator lies
in the seed, the index bound forces the seed into [W,G_a]N. Normalization
then puts its entire G_a orbit span there. The proof retains the literal
saturated carrier W = conjugatesIn Z_v G_a joined with N throughout.

An actual edge product A Q_a = T_t gives an actor image of order four in
the original SL3(2) quotient. The already published kernel transfer turns
the seed-commutator obstruction into injectivity, which forces this actor
to move W/N. This proves the conditional ambient generation equality and
applies `OrbitModule.full_of_generation` to the original quotient action.
No small-involution, quotient recognition or dual orientation is used.

The first actor is literally hatW at path indices 8,10,12. Its product
follows from (4.5.1)(iv) at the reversed configuration (8,6,4,5), the turn
at 8, and (4.5.3)(i) at (6,8), (6,4) and (10,12). Its commutator bound
is (4.5.3)(iii) at (8,10,12). These preceding clauses have producer
`qt-c01-ms93-core-factors-early-layers`; orbit containment is (4.5.4)(ii),
with producer `qt-c01-ms93-higher-orbit-geometry`.

This module does not yet establish the task's source-only generation
theorem. Its obstruction premise must be supplied by the first proof in
`Dynamics` or by `qt-c01-ms93-second-layer-delta-kernel`. Constructing the
delta actor and justifying its source clauses belongs to the existing
`qt-c01-ms93-second-layer-delta-actor` producer. No regular extension at
delta or containment of N in the raw orbit span is assumed here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.5.1)--(4.5.4), printed pp.896--899, especially p.899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Generation
open NormalizerTransfer

private theorem span_le {G : Type*} [Group G] {Z P J : Subgroup G}
    (hZ : Z ≤ J) (hn : P ≤ normalizer J) : conjugatesIn Z P ≤ J := by
  apply iSup_le
  intro g
  exact (map_mono hZ).trans
    (mem_normalizer_iff_map_conj_eq.mp (hn (P.inv_mem g.property))).le

private theorem generation_of_seed_index {G : Type*} [Group G]
    (Z P N A : Subgroup G) [Finite Z]
    (hN : P ≤ normalizer N) (hA : A ≤ P)
    (hi : N.relIndex Z ≤ 2)
    (hb : ⁅conjugatesIn Z P ⊔ N, A⁆ ≤ Z)
    (hm : ¬ ⁅conjugatesIn Z P ⊔ N, A⁆ ≤ N) :
    ⁅conjugatesIn Z P ⊔ N, P⁆ ⊔ N = conjugatesIn Z P ⊔ N := by
  let W := conjugatesIn Z P ⊔ N
  let D := ⁅W,P⁆ ⊔ N
  let E := N ⊓ Z
  let K := D ⊓ Z
  have hNW : N ≤ W := le_sup_right
  have hnW : P ≤ normalizer W :=
    (le_inf (conjugatesIn_normalized _ _) hN).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hnD : P ≤ normalizer D :=
    (le_inf (normalizer_commutator_ge_right W P) hN).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hEK : E ≤ K := inf_le_inf (show N ≤ D from le_sup_right) le_rfl
  have hKZ : K ≤ Z := inf_le_right
  let : Finite K := Finite.of_injective (inclusion hKZ) (inclusion_injective _)
  have hmoveK : ⁅W,A⁆ ≤ K :=
    le_inf ((commutator_mono le_rfl hA).trans le_sup_left) hb
  have hnot : ¬ K ≤ E := fun h => hm (hmoveK.trans (h.trans inf_le_left))
  have hpos : 0 < E.relIndex K := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hne : E.relIndex K ≠ 1 := fun h => hnot (relIndex_eq_one.mp h)
  have htwo : 2 ≤ E.relIndex K := by omega
  have hpos' : 0 < K.relIndex Z := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hmul := relIndex_mul_relIndex E K Z hEK hKZ
  have hbound : E.relIndex Z ≤ 2 := by simpa only [E, inf_relIndex_right] using hi
  have hindex : K.relIndex Z = 1 := by nlinarith
  have hZD : Z ≤ D := (relIndex_eq_one.mp hindex).trans inf_le_left
  apply le_antisymm
  · exact sup_le (le_normalizer_iff_commutator_le_left.mp hnW) hNW
  · exact sup_le (span_le hZD hnD) le_sup_right

variable {M : Type*} [Group M] {R L : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem path_color (p : Higher.SourcePath (alpha R))
    {i : ℕ} (hi : Even i) (hle : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; exact hle)).mpr hi

/-- The actual edge at index seven bounds the seed modulo the denominator. -/
theorem first_seed_index_le_two [Finite M] (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R)) :
    (hatV R (alpha R) (p.walk.getVert 6)).relIndex (Z R (p.walk.getVert 8)) ≤ 2 := by
  have hc7 : Adjacent R (p.walk.getVert 6) (p.walk.getVert 7) :=
    (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 6) (j := 7) (by decide) (by decide)))
  have hd7 : Adjacent R (p.walk.getVert 8) (p.walk.getVert 7) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 7) (j := 8) (by decide) (by decide))))
  have hZ : Z R (p.walk.getVert 7) ≤ hatV R (alpha R) (p.walk.getVert 6) :=
    (Escape.EdgeTransfer.edge_Z_le _ _ (path_color p (by decide) (by decide)) hc7).trans
      (PathCentrality.Z_le_localZSpan R _ _)
  let := finite_stabilizer R (p.walk.getVert 8)
  let : Finite (Z R (p.walk.getVert 8)) := Finite.of_injective
    (inclusion (Z_le_stabilizer R _)) (inclusion_injective _)
  exact (relIndex_le_of_le_left hZ (by exact index_ne_zero_of_finite)).trans_eq
    (earlier.edge_Z_index _ _ (path_color p (by decide) (by decide)) hd7)

/-- Delta's transported edge gives the same bound, without a new path. -/
theorem delta_seed_index_le_two [Finite M] (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p) :
    (hatV R (alpha R) (p.walk.getVert 6)).relIndex (Z R δ.vertex) ≤ 2 := by
  let t := act R δ.transporter (p.walk.getVert 5)
  have ha5 : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using (cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp
        (p.dist (i := 4) (j := 5) (by decide) (by decide)))
  have hc5 : Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 5) (j := 6) (by decide) (by decide))))
  have hvt : Adjacent R δ.vertex t := by
    rw [δ.vertex_eq]
    exact (adjacent_act_iff R δ.transporter _ _).mpr ha5
  have hct : Adjacent R (p.walk.getVert 6) t := by
    have hh := (adjacent_act_iff R δ.transporter _ _).mpr hc5
    have hf : act R δ.transporter (p.walk.getVert 6) = p.walk.getVert 6 :=
      δ.transporter.property
    rwa [hf] at hh
  have hZ : Z R t ≤ hatV R (alpha R) (p.walk.getVert 6) :=
    (Escape.EdgeTransfer.edge_Z_le _ _ (path_color p (by decide) (by decide)) hct).trans
      (PathCentrality.Z_le_localZSpan R _ _)
  let := finite_stabilizer R δ.vertex
  let : Finite (Z R δ.vertex) := Finite.of_injective
    (inclusion (Z_le_stabilizer R _)) (inclusion_injective _)
  exact (relIndex_le_of_le_left hZ (by exact index_ne_zero_of_finite)).trans_eq
    (earlier.edge_Z_index _ _ (delta_color δ) hvt)

private theorem factor_le_Q_of_dist (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R)) {v : Vertex R}
    (hv : color R v = false) (hd : (cosetGraph R).dist (alpha R) v ≤ 4)
    (horbit : conjugatesIn (Z R v) (stabilizer R (alpha R)) ≤ Q R v) :
    orbitFactor p v ≤ Q R v := by
  refine sup_le horbit ?_
  exact (hatV_le_radius R p.two_step_distances.1.le).trans
    ((Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le v (alpha R) 2 6
      (by omega)).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q v hv 6
        (by rw [earlier.distance]; decide)))

/-- One nonzero actor commutator fills the seed modulo N, hence its orbit span.
The noncontainment premise is an explicit remaining obligation; it is not
asserted to follow from the preceding source commutator bound alone. -/
theorem generation_of_actor_movement [Finite M] (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    {v : Vertex R} (hv : v = p.walk.getVert 8 ∨ v = δ.vertex)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R (alpha R))
    (horbit : conjugatesIn (Z R v) (stabilizer R (alpha R)) ≤ Q R v)
    (hcomm : ⁅A,Q R v⁆ ≤ Z R v)
    (hmove : ¬ ⁅orbitFactor p v,A⁆ ≤ hatV R (alpha R) (p.walk.getVert 6)) :
    ⁅orbitFactor p v,stabilizer R (alpha R)⁆ ⊔
      hatV R (alpha R) (p.walk.getVert 6) = orbitFactor p v := by
  have hcolor : color R v = false := by
    rcases hv with rfl | rfl
    · exact path_color p (by decide) (by decide)
    · exact delta_color δ
  have hdist : (cosetGraph R).dist (alpha R) v ≤ 4 := by
    rcases hv with rfl | rfl
    · exact (show (cosetGraph R).dist (alpha R) (p.walk.getVert 8) = 4 by
        simpa only [p.center_eq] using p.dist (i := 4) (j := 8) (by decide) (by decide)).le
    · have ht := (cosetGraph_connected R).dist_triangle
        (u := alpha R) (v := p.walk.getVert 6) (w := δ.vertex)
      have hca := p.two_step_distances.1
      have hdc := delta_dist_middle δ
      rw [SimpleGraph.dist_comm (u := p.walk.getVert 6) (v := alpha R)] at hca
      rw [SimpleGraph.dist_comm (u := δ.vertex)] at hdc
      omega
  have hi : (hatV R (alpha R) (p.walk.getVert 6)).relIndex (Z R v) ≤ 2 := by
    rcases hv with rfl | rfl
    · exact first_seed_index_le_two earlier p
    · exact delta_seed_index_le_two earlier δ
  have hb : ⁅orbitFactor p v,A⁆ ≤ Z R v := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (factor_le_Q_of_dist earlier p hcolor hdist horbit)).trans hcomm
  let := finite_stabilizer R v
  let : Finite (Z R v) := Finite.of_injective
    (inclusion (Z_le_stabilizer R _)) (inclusion_injective _)
  exact generation_of_seed_index _ _ _ _ (hatV_normalized R _ _) hA hi hb hmove

/-- Application to the recorded quotient action for either actual factor.
The actor movement premise remains explicit in this reduction. -/
theorem full_of_actor_movement [Finite M] (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    {v : Vertex R} (hv : v = p.walk.getVert 8 ∨ v = δ.vertex)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R (alpha R))
    (horbit : conjugatesIn (Z R v) (stabilizer R (alpha R)) ≤ Q R v)
    (hcomm : ⁅A,Q R v⁆ ≤ Z R v)
    (hmove : ¬ ⁅orbitFactor p v,A⁆ ≤ hatV R (alpha R) (p.walk.getVert 6))
    (s : OrbitModule source p v) :
    letI := s.normal; commutatorAction s.action.range (OrbitSpace p v) = ⊤ :=
  s.full_of_generation (generation_of_actor_movement earlier δ hv A hA horbit hcomm hmove)

private theorem actor_le_of_product
    {t : Vertex R} (ht : Adjacent R (alpha R) t)
    {A : Subgroup (FreeAmalgam R)}
    (hprod : (A : Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R))) : A ≤ stabilizer R (alpha R) := by
  intro x hx
  have hxT : x ∈ Q R t := by
    rw [← SetLike.mem_coe, ← hprod]
    exact ⟨x, hx, 1, (Q R (alpha R)).one_mem, mul_one x⟩
  exact hxT.2 _ (adjacent_symm R ht)

private theorem actor_moves_of_faithful [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} {v t : Vertex R}
    (s : OrbitModule source p v) (ht : Adjacent R (alpha R) t)
    {A : Subgroup (FreeAmalgam R)}
    (hprod : (A : Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)))
    (hf : letI := s.normal; Function.Injective s.action) :
    ¬ ⁅orbitFactor p v,A⁆ ≤ hatV R (alpha R) (p.walk.getVert 6) := by
  let := s.normal
  intro htrivial
  have hA := actor_le_of_product ht hprod
  have hk : Displacement.actorImage source A ≤ s.action.ker := by
    rintro _ ⟨m, hm, rfl⟩
    change s.action (source.projection m) = 1
    apply MulEquiv.ext
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      let y : orbitFactor p v := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
        le_normalizer_iff.mp (orbitFactor_normalized p v) _ (hA hm) _ x.property⟩
      change s.action (source.projection m) (QuotientGroup.mk x) = QuotientGroup.mk x
      rw [s.conjugation m x y rfl]
      apply QuotientGroup.eq_iff_div_mem.mpr
      change embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ /
        (x : FreeAmalgam R) ∈ hatV R (alpha R) (p.walk.getVert 6)
      have hh : ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ ⁅orbitFactor p v,A⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator hm x.property
      simpa only [commutatorElement_def, div_eq_mul_inv] using htrivial hh
  have he : Displacement.actorImage source A = ⊥ :=
    le_bot_iff.mp (hk.trans (s.action.ker_eq_bot_iff.mpr hf).le)
  have hc := (Displacement.edge_product_natural_card source common earlier ht hprod).2
  rw [he, card_bot] at hc
  omega

/-- Ambient generation from an actual actor and the seed-commutator obstruction.
The product and obstruction must be supplied by their geometric producers.
Faithfulness is deduced internally using the published kernel transfer. -/
theorem generation_of_edge_product_and_obstruction [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    {v : Vertex R} (hv : v = p.walk.getVert 8 ∨ v = δ.vertex)
    (s : OrbitModule source p v) {t : Vertex R} (ht : Adjacent R (alpha R) t)
    {A : Subgroup (FreeAmalgam R)}
    (hprod : (A : Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)))
    (horbit : conjugatesIn (Z R v) (stabilizer R (alpha R)) ≤ Q R v)
    (hcomm : ⁅A,Q R v⁆ ≤ Z R v)
    (hbad : ¬ stabilizer R (alpha R) ≤ normalizer
      (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),Z R v⁆ :
        Subgroup (FreeAmalgam R))) :
    ⁅orbitFactor p v,stabilizer R (alpha R)⁆ ⊔
      hatV R (alpha R) (p.walk.getVert 6) = orbitFactor p v := by
  exact generation_of_actor_movement earlier δ hv A (actor_le_of_product ht hprod)
    horbit hcomm (actor_moves_of_faithful common earlier s ht hprod
      (s.faithful_of_not_normalized_commutator earlier hbad))

/-- Construct the quotient action from the literal preceding clauses before
applying the ambient generation reduction. Here `hab` and `horbit` are the
actual (4.5.4)(ii) instance, `hbase` is (4.5.3)(iii) at a, and `hcomm` is
the corresponding clause for the supplied actor. Only the actor's geometric
product and the seed-commutator obstruction remain additional obligations.
Delta's generation equation supplies its seed containment in this proof. -/
theorem generation_of_source_actor_and_obstruction [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    {v : Vertex R} (hv : v = p.walk.getVert 8 ∨ v = δ.vertex)
    {t : Vertex R} (ht : Adjacent R (alpha R) t)
    {A : Subgroup (FreeAmalgam R)}
    (hprod : (A : Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)))
    (hab : IsMulCommutative (conjugatesIn (Z R v) (stabilizer R (alpha R))))
    (horbit : conjugatesIn (Z R v) (stabilizer R (alpha R)) ≤ Q R v)
    (hbase : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (alpha R)⁆ ≤ Z R (alpha R))
    (hcomm : ⁅A,Q R v⁆ ≤ Z R v)
    (hbad : ¬ stabilizer R (alpha R) ≤ normalizer
      (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),Z R v⁆ :
        Subgroup (FreeAmalgam R))) :
    ⁅orbitFactor p v,stabilizer R (alpha R)⁆ ⊔
      hatV R (alpha R) (p.walk.getVert 6) = orbitFactor p v := by
  have hseed : Z R v ≤ hatV R (p.walk.getVert 6) (p.walk.getVert 8) := by
    rcases hv with rfl | rfl
    · exact first_seed_le p
    · exact delta_seed_le δ
  have hcolor : color R v = false := by
    rcases hv with rfl | rfl
    · exact path_color p (by decide) (by decide)
    · exact delta_color δ
  obtain ⟨s⟩ := orbitModule source earlier p hseed hcolor hab hbase
  exact generation_of_edge_product_and_obstruction common earlier δ hv s ht
    hprod horbit hcomm hbad

/-- Use the literal forward hat-W actor for the first orbit factor.
The three hat-V equalities are (4.5.3)(i); the product is reversed
(4.5.1)(iv); the hat-W commutator is translated (4.5.3)(iii). The final
obstruction is already proved in the parent Dynamics module, and remains
explicit here to preserve the required acyclic import boundary. -/
theorem first_generation_of_obstruction [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hV6 : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hV6rev : hatV R (p.walk.getVert 6) (p.walk.getVert 4) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hV10 : hatV R (p.walk.getVert 10) (p.walk.getVert 12) =
      Vcirc R (p.walk.getVert 10) ⊔ Z R (p.walk.getVert 10))
    (hprod : (hatW R (p.walk.getVert 8) (p.walk.getVert 6) (p.walk.getVert 4) :
      Set (FreeAmalgam R)) * (Q R (p.walk.getVert 4) : Set (FreeAmalgam R)) =
      (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (horbit : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8))
    (hcomm : ⁅hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8))
    (s : OrbitModule source p (p.walk.getVert 8))
    (hbad : ¬ stabilizer R (alpha R) ≤ normalizer
      (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
        Z R (p.walk.getVert 8)⁆ : Subgroup (FreeAmalgam R))) :
    ⁅orbitFactor p (p.walk.getVert 8),stabilizer R (alpha R)⁆ ⊔
      hatV R (alpha R) (p.walk.getVert 6) = orbitFactor p (p.walk.getVert 8) := by
  have ht : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using (cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp
        (p.dist (i := 4) (j := 5) (by decide) (by decide)))
  exact generation_of_edge_product_and_obstruction common earlier δ (Or.inl rfl) s ht
    (Displacement.first_actor_product p hV6 hV6rev hV10 hprod) horbit hcomm hbad

/-- The constructed ambient equality gives full movement on the actual quotient.
This is conditional on the named geometric obstruction and actor, not a
claim that either source argument has been discharged by this module. -/
theorem full_of_edge_product_and_obstruction [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    {v : Vertex R} (hv : v = p.walk.getVert 8 ∨ v = δ.vertex)
    (s : OrbitModule source p v) {t : Vertex R} (ht : Adjacent R (alpha R) t)
    {A : Subgroup (FreeAmalgam R)}
    (hprod : (A : Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)))
    (horbit : conjugatesIn (Z R v) (stabilizer R (alpha R)) ≤ Q R v)
    (hcomm : ⁅A,Q R v⁆ ≤ Z R v)
    (hbad : ¬ stabilizer R (alpha R) ≤ normalizer
      (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),Z R v⁆ :
        Subgroup (FreeAmalgam R))) :
    letI := s.normal; commutatorAction s.action.range (OrbitSpace p v) = ⊤ :=
  s.full_of_generation
    (generation_of_edge_product_and_obstruction common earlier δ hv s ht hprod horbit hcomm hbad)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Generation
