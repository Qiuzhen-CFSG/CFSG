module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.DeltaActor.Transport
/-!
# Nondegeneracy of the source delta

The genuine natural section and local residual generation identify the middle
hat-V quotient as a group of order eight. Each of Z_a and Z_d contributes at
most a factor of two, so delta's generation equation forces its third seed
outside their join.

The literal relative normality in (4.5.2)(i), at a, the edge p[5] and c,
then shows that delta's given transporter moves that edge. The resulting
four-edge walk is simple in the actual amalgam tree. Hence delta is four
steps from a and three from p[5], and its hat-W actor lies in Q_(p[5]).

The only additional earlier source inputs are (4.5.3)(i) at c and
(4.5.2)(i) at the original path. In the last conditional consumer the
original (4.5.3)(iii) commutator is transported by Transport. Coverage of
Q_(p[5])/Q_a is still an obligation, retained as a strict image bound.
These are completed geometric lemmas, not a proof of that coverage.

Source: Meierfrankenfeld--Stellmacher (1993), pp.896--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
 {geometry : Geometry R} {source : LocalSource L R}

omit [Finite M] in
private theorem radius_commutator_le_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (ha : color R a = false) :
    ⁅V R a, Q R a⁆ ≤ Z R a := by
  let := PathCentrality.V_elementary_of_four_lt R (a := a) ha
    (by rw [earlier.distance]; decide)
  have hVQ := PathCentrality.V_le_Q R (a := a) ha common.large_distance
  have hcommV : ⁅V R a, Q R a⁆ ≤ V R a :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
        (DistanceEight.V_normalized R a))
  rw [← common.X_eq_Z a ha]
  intro x hx
  apply mem_omegaCenter_iff.mpr
  refine ⟨hVQ (hcommV hx), elemPow_eq_one_of_isElementaryAbelian x (hcommV hx), ?_⟩
  obtain ⟨z,hz,rfl⟩ := earlier.centrality a ha hx
  intro q hq
  exact congrArg Subtype.val ((mem_center_iff.mp hz)
    ⟨q, (show Q R a ≤ stabilizer R a from fun _ h => h.1) hq⟩)

/-- The preceding natural section gives the exact first-layer index, using the
actual residual-plus-kernel generation and the literal (4.5.3)(i) equality. -/
theorem hatV_index_eight (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c : Vertex R} (ha : color R a = false)
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a) :
    (Z R a).relIndex (hatV R a c) = 8 := by
  obtain ⟨s⟩ := earlier.natural_section a ha
  let S := stabilizer R a
  let H₀ := (V R a).subgroupOf S
  let N₀ := (Z R a).subgroupOf S
  let Q₀ := (Q R a).subgroupOf S
  let D := Escape.radicalPreimage Q₀ H₀ N₀
  let F := Escape.movingPreimage Q₀ H₀ N₀
  have hZ : N₀.map S.subtype = Z R a :=
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)
  have hH : H₀.map S.subtype = V R a :=
    map_subgroupOf_eq_of_le s.local_group
  have hQ : Q₀.map S.subtype = Q R a :=
    map_subgroupOf_eq_of_le (fun _ hx => hx.1)
  have hD : D.map S.subtype = Z R a := by
    change (N₀ ⊔ ⁅H₀,Q₀⁆).map S.subtype = _
    rw [Subgroup.map_sup, map_commutator, hZ, hH, hQ]
    exact sup_eq_left.mpr (radius_commutator_le_Z common earlier ha)
  have hF : F.map S.subtype = Z R a ⊔ ⁅V R a,S⁆ := by
    change (D ⊔ ⁅H₀,(⊤ : Subgroup S)⁆).map S.subtype = _
    rw [Subgroup.map_sup, map_commutator, hD, hH, ← MonoidHom.range_eq_map, S.range_subtype]
  have hsize : (Z R a).relIndex (F.map S.subtype) = 8 := by
    rw [← hD, relIndex_map_map_of_injective _ _ S.subtype_injective]
    exact s.module_section.moving_quotient_card
  have hle : hatV R a c ≤ F.map S.subtype := by
    rw [hVa,hF]
    exact sup_le ((commutator_mono le_rfl (Ltilde_le_stabilizer _)).trans le_sup_right)
      le_sup_left
  have hpre : S ≤ commutatorPreimage S (V R a) (hatV R a c) := by
    change stabilizer R a ≤ _
    rw [← source.local_generation a ha]
    refine sup_le ?_ ?_
    · apply le_commutatorPreimage (Ltilde_le_stabilizer _)
      rw [commutator_comm]
      exact (show Vcirc R a ≤ hatV R a c by rw [hVa]; exact le_sup_left)
    · apply le_commutatorPreimage (show Q R a ≤ S from fun _ hx => hx.1)
      rw [commutator_comm]
      exact (radius_commutator_le_Z common earlier ha).trans (hVa ▸ le_sup_right)
  have hrev : F.map S.subtype ≤ hatV R a c := by
    rw [hF]
    refine sup_le (hVa ▸ le_sup_right) ?_
    rw [commutator_comm]
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _
        (hatV_normalized R a c))
  rwa [le_antisymm hrev hle] at hsize

private theorem relIndex_normalized_sup {G : Type*} [Group G]
    (A C : Subgroup G) (hn : C ≤ normalizer (A : Set G)) :
    A.relIndex (A ⊔ C) = A.relIndex C := by
  let J := A ⊔ C
  let : (A.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have he := relIndex_sup_left (C.subgroupOf J) (A.subgroupOf J)
  rw [← subgroupOf_sup (show A ≤ J from le_sup_left) (show C ≤ J from le_sup_right),
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf (show C ≤ J from le_sup_right)] at he
  exact he

private theorem sup_index_le {G : Type*} [Group G]
    {N A B V : Subgroup G} [Finite V] [IsMulCommutative V]
    (hN : N ≤ V) (hA : A ≤ V) (hB : B ≤ V) :
    N.relIndex (A ⊔ B) ≤ N.relIndex A * N.relIndex B := by
  have hn {X Y : Subgroup G} (hX : X ≤ V) (hY : Y ≤ V) :
      Y ≤ normalizer (X : Set G) :=
    (hY.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans
      ((centralizer_le hX).trans (Subgroup.centralizer_le_normalizer _))
  let T := N ⊔ A
  have hT : T ≤ V := sup_le hN hA
  have hTB : T ⊔ B ≤ V := sup_le hT hB
  let : Finite B := Finite.of_injective (inclusion hB) (inclusion_injective _)
  let : Finite (T ⊔ B : Subgroup G) :=
    Finite.of_injective (inclusion hTB) (inclusion_injective _)
  have hb : T.relIndex B ≤ N.relIndex B :=
    relIndex_le_of_le_left (show N ≤ T from le_sup_left) index_ne_zero_of_finite
  have hm := relIndex_mul_relIndex N T (T ⊔ B) le_sup_left le_sup_left
  rw [relIndex_normalized_sup T B (hn hT hB),
    relIndex_normalized_sup N A (hn hN hA)] at hm
  have hi := relIndex_le_of_le_right
    (show A ⊔ B ≤ T ⊔ B from sup_le_sup le_sup_right le_rfl)
    (show N.relIndex (T ⊔ B) ≠ 0 from index_ne_zero_of_finite)
  exact hi.trans (hm.symm.le.trans (Nat.mul_le_mul_left _ hb))

omit [Finite M] in
private theorem path_color (p : Higher.SourcePath (alpha R))
    {i : ℕ} (hi : Even i) (hle : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; exact hle)).mpr hi

/-- The third seed in delta's given generation equation cannot lie in the
join of the two original seeds. No choice of a replacement delta is made. -/
theorem delta_seed_not_le_pair (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6)) :
    ¬ Z R δ.vertex ≤ Z R (alpha R) ⊔ Z R (p.walk.getVert 8) := by
  let c := p.walk.getVert 6
  let d := p.walk.getVert 8
  have hc : color R c = false := path_color p (by decide) (by decide)
  have hd : color R d = false := path_color p (by decide) (by decide)
  have ha5 : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using (cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp (p.dist (i := 4) (j := 5) (by decide) (by decide)))
  have hc5 : Adjacent R c (p.walk.getVert 5) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp (p.dist (i := 5) (j := 6) (by decide) (by decide))))
  have hc7 : Adjacent R c (p.walk.getVert 7) :=
    (cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp (p.dist (i := 6) (j := 7) (by decide) (by decide)))
  have hd7 : Adjacent R d (p.walk.getVert 7) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp (p.dist (i := 7) (j := 8) (by decide) (by decide))))
  have hZa : Z R (alpha R) ≤ V R c :=
    (PathCentrality.Z_le_localZSpan R _ _).trans
      (hatV_le_radius R (by rw [SimpleGraph.dist_comm]; exact p.two_step_distances.1.le))
  have hZd : Z R d ≤ V R c :=
    (PathCentrality.Z_le_localZSpan R _ _).trans (hatV_le_radius R p.two_step_distances.2.1.le)
  let := finite_stabilizer R c
  let : Finite (V R c) := Finite.of_injective
    (inclusion (geometry.V_local c hc (by rw [(geometry.distance_constant c hc).trans earlier.distance]; decide)))
    (inclusion_injective _)
  let : Finite (Z R (alpha R)) := Finite.of_injective (inclusion hZa) (inclusion_injective _)
  let : Finite (Z R d) := Finite.of_injective (inclusion hZd) (inclusion_injective _)
  let := PathCentrality.V_elementary_of_four_lt R hc (by rw [earlier.distance]; decide)
  have hiA : (Z R c).relIndex (Z R (alpha R)) ≤ 2 :=
    (relIndex_le_of_le_left (Escape.EdgeTransfer.edge_Z_le c _ hc hc5)
      (show (Z R (p.walk.getVert 5)).relIndex (Z R (alpha R)) ≠ 0 from
        index_ne_zero_of_finite)).trans_eq (earlier.edge_Z_index _ _ rfl ha5)
  have hiB : (Z R c).relIndex (Z R d) ≤ 2 :=
    (relIndex_le_of_le_left (Escape.EdgeTransfer.edge_Z_le c _ hc hc7)
      (show (Z R (p.walk.getVert 7)).relIndex (Z R d) ≠ 0 from
        index_ne_zero_of_finite)).trans_eq (earlier.edge_Z_index _ _ hd hd7)
  have hsmall : (Z R c).relIndex (Z R (alpha R) ⊔ Z R d) ≤ 4 := by
    exact (sup_index_le (V := V R c) (Z_le_VBall R c 2) hZa hZd).trans
      (by nlinarith : (Z R c).relIndex (Z R (alpha R)) * (Z R c).relIndex (Z R d) ≤ 4)
  intro hdelta
  have he : hatV R c d = Z R (alpha R) ⊔ Z R d := by
    rw [δ.generation]
    exact le_antisymm (sup_le (sup_le le_sup_left hdelta) le_sup_right)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hbig := hatV_index_eight common earlier hc hVc
  rw [he] at hbig
  omega


/-- Relative normality (4.5.2)(i) at the original path forces its edge to
move under delta's actual transporter. The displayed normalizer inclusion is
normality of Z_a in G_c intersect G_(p[5]); all groups remain ambient subgroups. -/
theorem delta_transported_edge_ne (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hnormal : stabilizer R (p.walk.getVert 6) ⊓ stabilizer R (p.walk.getVert 5) ≤
      normalizer (Z R (alpha R) : Set (FreeAmalgam R))) :
    act R δ.transporter (p.walk.getVert 5) ≠ p.walk.getVert 5 := by
  intro he
  have hg5 : (δ.transporter : FreeAmalgam R) ∈ stabilizer R (p.walk.getVert 5) := he
  have hZ : Z R δ.vertex = Z R (alpha R) := by
    rw [δ.vertex_eq, Z_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      (hnormal ⟨(stabilizer R _).inv_mem δ.transporter.property, (stabilizer R _).inv_mem hg5⟩)
  apply delta_seed_not_le_pair common earlier δ hVc
  rw [hZ]
  exact le_sup_left

/-- The transported two-edge segment and original two-edge segment form
a simple four-edge path, so the distance from a to the given delta is four. -/
theorem delta_dist_base_eq_four (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hnormal : stabilizer R (p.walk.getVert 6) ⊓ stabilizer R (p.walk.getVert 5) ≤
      normalizer (Z R (alpha R) : Set (FreeAmalgam R))) :
    (cosetGraph R).dist (alpha R) δ.vertex = 4 := by
  let t := act R δ.transporter (p.walk.getVert 5)
  have ha5 : (cosetGraph R).Adj (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 4) (j := 5) (by decide) (by decide))
  have h5c : (cosetGraph R).Adj (p.walk.getVert 5) (p.walk.getVert 6) :=
    SimpleGraph.dist_eq_one_iff_adj.mp (p.dist (i := 5) (j := 6) (by decide) (by decide))
  have hct : (cosetGraph R).Adj (p.walk.getVert 6) t := by
    have h := (adjacent_act_iff R δ.transporter _ _).mpr
      ((cosetGraph_adj R _ _).mp h5c.symm)
    have hc : act R δ.transporter (p.walk.getVert 6) = p.walk.getVert 6 :=
      δ.transporter.property
    rw [hc] at h
    exact (cosetGraph_adj R _ _).mpr h
  have htδ : (cosetGraph R).Adj t δ.vertex := by
    rw [δ.vertex_eq]
    exact (cosetGraph_adj R _ _).mpr ((adjacent_act_iff R δ.transporter _ _).mpr
      ((cosetGraph_adj R _ _).mp ha5.symm))
  have h5t : p.walk.getVert 5 ≠ t :=
    (delta_transported_edge_ne common earlier δ hVc hnormal).symm
  have haδ : alpha R ≠ δ.vertex := by
    intro h
    apply delta_seed_not_le_pair common earlier δ hVc
    rw [← h]
    exact le_sup_left
  have hac : alpha R ≠ p.walk.getVert 6 := by
    intro h
    have hc := p.two_step_distances.1
    simp only [← h, SimpleGraph.dist_self] at hc
    omega
  have hcδ : p.walk.getVert 6 ≠ δ.vertex := by
    intro h
    have hc := delta_dist_middle δ
    rw [h, SimpleGraph.dist_self] at hc
    omega
  have h5δ : p.walk.getVert 5 ≠ δ.vertex := by
    intro h
    have hc := adjacent_color_ne R ((cosetGraph_adj R _ _).mp ha5)
    rw [h, delta_color δ] at hc
    exact hc rfl
  have hat : alpha R ≠ t := by
    intro h
    have hc := adjacent_color_ne R ((cosetGraph_adj R _ _).mp htδ)
    rw [← h, delta_color δ] at hc
    exact hc rfl
  let w := SimpleGraph.Walk.cons ha5 (.cons h5c (.cons hct (.cons htδ .nil)))
  have hw : w.IsPath := by
    simp [w, SimpleGraph.Walk.cons_isPath_iff, ha5.ne, h5c.ne, hct.ne, htδ.ne,
      h5t, haδ, hac, hcδ, h5δ, hat]
  obtain ⟨v,hv⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist (alpha R) δ.vertex
  have heq : w = v := Subtype.mk.inj
    ((cosetGraph_isTree R).isAcyclic.subsingleton_path _ _ |>.elim
      ⟨w,hw⟩ ⟨v,v.isPath_of_length_eq_dist hv⟩)
  have hlen : w.length = 4 := rfl
  rw [heq, hv] at hlen
  exact hlen


/-- Delta is three steps from the original edge vertex p[5]. -/
theorem delta_dist_original_edge (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hnormal : stabilizer R (p.walk.getVert 6) ⊓ stabilizer R (p.walk.getVert 5) ≤
      normalizer (Z R (alpha R) : Set (FreeAmalgam R))) :
    (cosetGraph R).dist δ.vertex (p.walk.getVert 5) = 3 := by
  have hda : (cosetGraph R).dist δ.vertex (alpha R) = 4 := by
    rw [SimpleGraph.dist_comm]
    exact delta_dist_base_eq_four common earlier δ hVc hnormal
  have hac : (cosetGraph R).dist (p.walk.getVert 5) (alpha R) = 1 := by
    simpa only [p.center_eq, SimpleGraph.dist_comm] using
      p.dist (i := 4) (j := 5) (by decide) (by decide)
  have hc5 : (cosetGraph R).dist (p.walk.getVert 6) (p.walk.getVert 5) = 1 := by
    rw [SimpleGraph.dist_comm]
    exact p.dist (i := 5) (j := 6) (by decide) (by decide)
  have hupper := (cosetGraph_connected R).dist_triangle
    (u := δ.vertex) (v := p.walk.getVert 6) (w := p.walk.getVert 5)
  have hlower := (cosetGraph_connected R).dist_triangle
    (u := δ.vertex) (v := p.walk.getVert 5) (w := alpha R)
  rw [delta_dist_middle δ, hc5] at hupper
  rw [hda, hac] at hlower
  omega

/-- Radius and critical minimality put the actual candidate actor in the
original edge kernel. This establishes containment, not the product equality. -/
theorem delta_actor_le_original_edge (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hnormal : stabilizer R (p.walk.getVert 6) ⊓ stabilizer R (p.walk.getVert 5) ≤
      normalizer (Z R (alpha R) : Set (FreeAmalgam R))) :
    hatW R δ.vertex (p.walk.getVert 6) (alpha R) ≤ Q R (p.walk.getVert 5) :=
  Early.First.Layer.hatW_le_edge_kernel earlier (delta_color δ)
    (by rw [SimpleGraph.dist_comm]; exact (delta_dist_middle δ).le)
    (by rw [SimpleGraph.dist_comm]; exact p.two_step_distances.1.le)
    (delta_dist_original_edge common earlier δ hVc hnormal)

/-- Apply all the proved geometry to the actual orbit module. The remaining
strict image bound must still be supplied; it is not a preceding source clause. -/
theorem delta_small_and_separated_of_large_image
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (s : OrbitModule source p δ.vertex)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hnormal : stabilizer R (p.walk.getVert 6) ⊓ stabilizer R (p.walk.getVert 5) ≤
      normalizer (Z R (alpha R) : Set (FreeAmalgam R)))
    (himage : 2 < (Q R (alpha R)).relIndex
      (hatW R δ.vertex (p.walk.getVert 6) (alpha R)))
    (horbit : NormalizerTransfer.conjugatesIn (Z R δ.vertex)
      (stabilizer R (alpha R)) ≤ Q R δ.vertex)
    (hcomm : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (alpha R)⁆ ≤ Z R (alpha R)) : letI := s.normal
    Escape.Initial.Natural.Splitting.HasSmallInvolution s.action ∧
      DisplacementSeparation s.action common.natural.marking := by
  have ht : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using (cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp
        (p.dist (i := 4) (j := 5) (by decide) (by decide)))
  have hprod := Early.First.Layer.hatW_product_of_large_image earlier
    (delta_color δ) (R := R) rfl ht
    (by rw [SimpleGraph.dist_comm]; exact (delta_dist_middle δ).le)
    (by rw [SimpleGraph.dist_comm]; exact p.two_step_distances.1.le)
    (delta_dist_original_edge common earlier δ hVc hnormal) himage
  exact delta_small_and_separated_of_candidate_product source common earlier δ s
    hprod horbit hcomm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement

