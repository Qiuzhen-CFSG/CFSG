module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Dynamics.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.LocalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction
public import Theory.GroupTheory.Commutator.CentralizingFactor

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Geometry

/-!
# The delta centralizer obstruction

The actual transporter of delta and the turn at c identify its local Z-span
with hat V_c. Thus [hat W_a,Z_delta] lies in H_c. The original critical
window and turn put H_c inside the irreducible natural group U_a, while the
preceding numerical estimate gives |H_c| at most four.

If the delta commutator were trivial, its whole G_a orbit would centralize
hat W_a. Delta's generation equation expresses hat W_a as the join of the
two orbit factors. The first factor lies in Q_d, so both factors would
centralize Z_d. This contradicts the edge displacement of order four
obtained from the literal product hat W_a Q_d = T_(p[7]). Hence the delta
commutator has order strictly between one and eight, and irreducibility
excludes its normalization by G_a. The recorded quotient-conjugation formula
then gives faithfulness on every actual delta orbit quotient.

There are exactly two additional source premises: the setwise product
(4.5.1)(iv), produced by `qt-c01-ms93-core-factors-early-layers`, and
conjugatesIn(Z_d,G_a) <= Q_d from (4.5.4)(ii), produced by
`qt-c01-ms93-higher-orbit-geometry`. Their discharge and the independent
moving-generation argument remain with the parent source assembly. No
extension of delta to a regular path or quotient model is assumed.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.5.1)(iv--v), printed p.896; (4.5.4)(ii--iii), pp.898--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
open NormalizerTransfer
variable {M : Type*} [Group M] {R L : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R}

private theorem delta_natural_subgroup_dichotomy [Finite M]
    (common : CommonFacts R source geometry) (K : Subgroup (FreeAmalgam R))
    (hK : K ≤ U R (alpha R))
    (hn : stabilizer R (alpha R) ≤ normalizer K) :
    K = ⊥ ∨ K = U R (alpha R) := by
  open Escape.Propagation.Backward.Products.Selection.Choices in
  obtain ⟨model⟩ := localModel_nonempty source (PathCentrality.LocalCommutator.moduleFacts common)
    (alpha R) rfl
  let S := stabilizer R (alpha R)
  have hUS : U R (alpha R) ≤ S := (U_le_Z R _).trans (Z_le_stabilizer R _)
  let e := (subgroupOfEquivOfLe hUS).trans model.equiv
  let n : RankOnePairing.NaturalFactor model.projection ⊤ ((U R (alpha R)).subgroupOf S) ⊥ := {
    marking := MulEquiv.refl _
    coordinates := e.toMonoidHom
    surjective := e.surjective
    kernel := by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective, bot_subgroupOf]
    normalized := by
      intro g _
      rw [← subgroupOf_normalizer_eq hUS]
      exact U_normalized _ g.property
    action := by
      intro g _ x y h
      exact congrArg Multiplicative.toAdd (model.action g
        ((subgroupOfEquivOfLe hUS) x) ((subgroupOfEquivOfLe hUS) y)
        (congrArg Subtype.val h)) }
  have hm : (⊤ : Subgroup S).map model.projection = ⊤ :=
    map_top_of_surjective _ model.surjective
  have hnorm : (⊤ : Subgroup S) ≤ normalizer (K.subgroupOf S : Set S) := by
    intro g _
    rw [← subgroupOf_normalizer_eq (hK.trans hUS)]
    exact hn g.property
  rcases n.irreducible hm (K.subgroupOf S) (subgroupOf_mono S hK) hnorm with h | h
  · left
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), Subgroup.map_bot] using hh
  · right
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), map_subgroupOf_eq_of_le hUS] using hh

private theorem delta_path_color (p : Higher.SourcePath (alpha R))
    {i : ℕ} (hi : Even i) (hle : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; exact hle)).mpr hi

private theorem delta_middle_moving [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R)) :
    Vcirc R (p.walk.getVert 6) ≤ hatV R (p.walk.getVert 6) (alpha R) := by
  have hcrit : CriticalPair R (p.walk.getVert 0) (p.walk.getVert 8)
      (geometry.exists_critical _ (delta_path_color p (by decide) (by decide))) := by
    refine ⟨?_, (p.critical 0 (by decide) (by decide)).2⟩
    rw [(geometry.distance_constant _ (delta_path_color p (by decide) (by decide))).trans earlier.distance]
    exact p.dist (by decide) (by decide)
  have hmove := Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
    source common.large_distance (delta_path_color p (by decide) (by decide)) hcrit (s := p.walk.getVert 6)
  have hbefore : Escape.Before (p.walk.getVert 0) (p.walk.getVert 8)
      (p.walk.getVert 6) 2 := by
    constructor
    · exact p.dist (by decide) (by decide)
    · rw [p.dist (i := 0) (j := 6) (by decide) (by decide),
        p.dist (i := 0) (j := 8) (by decide) (by decide)]
  obtain ⟨g, hg, he⟩ := p.turns 6 (by decide) (by decide) (by decide)
  have ht := Escape.Propagation.Rigidity.moving_of_local_act common.large_distance
    (p.walk.getVert 6) (p.walk.getVert 8) (delta_path_color p (by decide) (by decide))
    (hmove hbefore) g hg
  rw [he, p.center_eq] at ht
  exact Early.moving_le_hatV source earlier (delta_path_color p (by decide) (by decide)) ht

/-- The transporter and the actual turn at c identify the delta span with
hat V_c. No regular path at delta is needed. -/
theorem delta_span_eq {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p) :
    hatV R (p.walk.getVert 6) δ.vertex =
      hatV R (p.walk.getVert 6) (p.walk.getVert 8) := by
  change PathCentrality.localZSpan R δ.vertex (p.walk.getVert 6) =
    PathCentrality.localZSpan R (p.walk.getVert 8) (p.walk.getVert 6)
  rw [δ.vertex_eq,
    PathCentrality.LocalCommutator.CriticalCase.span_eq_of_local_conjugator
      δ.transporter.property]
  obtain ⟨g, hg, he⟩ := p.turns 6 (by decide) (by decide) (by decide)
  have ht : act R g (p.walk.getVert 8) = alpha R := by
    simpa only [p.center_eq] using he
  simpa only [ht] using
    (PathCentrality.LocalCommutator.CriticalCase.span_eq_of_local_conjugator
      (a := p.walk.getVert 8) hg)

/-- The actual delta commutator lies in the middle H-layer. -/
theorem delta_displacement_le_H [Finite M] (source : LocalSource L R)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p) :
    ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Z R δ.vertex⁆ ≤
      H R (p.walk.getVert 6) := by
  have he : hatW R (alpha R) (p.walk.getVert 6) δ.vertex =
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
    unfold hatW
    rw [delta_span_eq δ]
  rw [← he, commutator_comm]
  apply Early.First.Layer.hatW_displacement_le_H source earlier
    (delta_path_color p (by decide) (by decide))
  · exact adjacent_symm R ((cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp
        (p.dist (i := 5) (j := 6) (by decide) (by decide))))
  · exact p.two_step_distances.1.le
  · exact (delta_dist_middle δ).le
  · simpa only [p.center_eq] using p.dist (i := 4) (j := 5) (by decide) (by decide)

private theorem delta_first_displacement_card [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R))
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R))) :
    Nat.card (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
      Z R (p.walk.getVert 8)⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  have hd := delta_path_color p (i := 8) (by decide) (by decide)
  have hdt : Adjacent R (p.walk.getVert 8) (p.walk.getVert 7) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 7) (j := 8) (by decide) (by decide))))
  have hc : Z R (p.walk.getVert 8) ≤ centralizer (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) :=
    commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ hd)
  rw [commutator_comm, ← commutator_eq_of_product_centralizing_factor hprod.symm hc]
  exact Early.First.Layer.edge_displacement_card common earlier hd hdt

/-- Generation by the two literal factors makes the delta displacement
nontrivial. Otherwise its entire orbit centralizes the second layer, and
(4.5.4)(ii) makes the first displacement trivial, contrary to (4.5.1)(iv).
The respective producers are qt-c01-ms93-higher-orbit-geometry and
qt-c01-ms93-core-factors-early-layers. -/
theorem delta_displacement_ne_bot [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (horbit : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8)) :
    (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Z R δ.vertex⁆ :
      Subgroup (FreeAmalgam R)) ≠ ⊥ := by
  intro hbot
  let W := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  have hseed : Z R δ.vertex ≤ centralizer (W : Set (FreeAmalgam R)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  have hspan : conjugatesIn (Z R δ.vertex) (stabilizer R (alpha R)) ≤
      centralizer (W : Set (FreeAmalgam R)) := by
    apply iSup_le
    intro g
    exact (map_mono hseed).trans
      (mem_normalizer_iff_map_conj_eq.mp
        (((hatW_normalized R _ _ _).trans (normalizer_le_normalizer_centralizer W))
          ((stabilizer R (alpha R)).inv_mem g.property))).le
  have hdelta : orbitFactor p δ.vertex ≤ centralizer (W : Set (FreeAmalgam R)) :=
    sup_le hspan (denominator_centralizes_second earlier p)
  have hd := delta_path_color p (i := 8) (by decide) (by decide)
  have hfirst : orbitFactor p (p.walk.getVert 8) ≤
      centralizer (Z R (p.walk.getVert 8) : Set (FreeAmalgam R)) :=
    (first_factor_le_Q earlier p horbit).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes _ hd)))
  have hZdW : Z R (p.walk.getVert 8) ≤ W :=
    (first_seed_le p).trans (Escape.Initial.Natural.conjugatesIn_contains _ _)
  have hW : W ≤ centralizer (Z R (p.walk.getVert 8) : Set (FreeAmalgam R)) := by
    dsimp only [W]
    rw [← δ.factors_generate]
    exact sup_le hfirst (hdelta.trans (centralizer_le hZdW))
  have hc := delta_first_displacement_card common earlier p hprod
  rw [commutator_eq_bot_iff_le_centralizer.mpr hW, card_bot] at hc
  omega

/-- The delta displacement is a nontrivial subgroup of H_c, hence has
order at most four. These are proved bounds on the actual amalgam subgroup. -/
theorem delta_displacement_card_bounds [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (horbit : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8)) :
    1 < Nat.card (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Z R δ.vertex⁆ :
      Subgroup (FreeAmalgam R)) ∧
    Nat.card (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Z R δ.vertex⁆ :
      Subgroup (FreeAmalgam R)) ≤ 4 := by
  let K := ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Z R δ.vertex⁆
  have hc := delta_path_color p (i := 6) (by decide) (by decide)
  have hKH := delta_displacement_le_H source earlier δ
  let := finite_stabilizer R (p.walk.getVert 6)
  let : Finite (H R (p.walk.getVert 6)) := Finite.of_injective
    (inclusion ((H_le_Z_of_central common hc (earlier.centrality _ hc)).trans
      (Z_le_stabilizer R _))) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKH) (inclusion_injective _)
  have hn : K ≠ ⊥ := delta_displacement_ne_bot common earlier δ hprod horbit
  have hcard : 1 < Nat.card K := by
    exact (Subgroup.one_lt_card_iff_ne_bot K).mpr hn
  exact ⟨hcard, (card_le_of_le hKH).trans (Early.H_card_le_four common earlier hc)⟩

/-- The delta centralizer obstruction in (4.5.4)(iii). Its only additional
source premises are (4.5.1)(iv) and the first orbit containment (4.5.4)(ii). -/
theorem delta_displacement_not_normalized [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (horbit : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8)) :
    ¬ stabilizer R (alpha R) ≤ normalizer
      (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Z R δ.vertex⁆ :
        Subgroup (FreeAmalgam R)) := by
  intro hn
  have hc := delta_path_color p (i := 6) (by decide) (by decide)
  have hHU : H R (p.walk.getVert 6) ≤ U R (alpha R) :=
    Early.H_le_neighbor_U common earlier hc
      (by rw [SimpleGraph.dist_comm]; exact p.two_step_distances.1)
      (delta_middle_moving common earlier p)
  have hle := (delta_displacement_le_H source earlier δ).trans hHU
  have hb := delta_displacement_card_bounds common earlier δ hprod horbit
  rcases delta_natural_subgroup_dichotomy common _ hle hn with h | h
  · rw [h, card_bot] at hb
    omega
  · rw [h, DistanceEight.U_card R common.natural] at hb
    omega

/-- Faithfulness of every recorded action on the actual delta orbit quotient,
with its literal relative denominator and conjugation formula. -/
theorem delta_factor_faithful [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (horbit : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8)) (s : OrbitModule source p δ.vertex) :
    letI := s.normal; Function.Injective s.action :=
  s.faithful_of_not_normalized_commutator earlier
    (delta_displacement_not_normalized common earlier δ hprod horbit)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
