module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Estimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Forward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Edges
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The original path in the large first-pairing image case

Forward nonnormality of Z_alpha Z_(alpha+2) proves that alpha is a moving
neighbor at the original second vertex. The full natural section gives
[V,Q,Ltilde] ≤ Z, hence [V,Q] ≤ B. For an incident layer W = V_t, the
subgroup Z[W,Q] is normalized by Q and by Ltilde. Neighbor transitivity
therefore puts [V,Q] inside every such W. This supplies the displacement
containment in V_(alpha+3) used on printed p.884. Critical minimality then
shows that V_c centralizes this third layer.

The final centralizer bound is proved separately by the three-subgroups
lemma and the same neighbor generation: [V,[Q,Ltilde]] ≤ D implies
[V,C_Q(V_t)] ≤ D. All normalization is relative to the vertex stabilizer.
The imported StepThree.Edges results use only transported (4.3.1), not any
conclusion of step (3) or the later escape argument.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2)(iv), (4.3.1)(iii),(vii),
and the first paragraph of (4.3.2)(2), printed pp.856--857 and 882--884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

theorem adjacent_V_le {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) : V R t ≤ V R a := by
  apply Geometry.V_le_of_h_neighbors ha hat
  intro d hdt
  apply le_iSup_of_le d
  apply le_iSup_of_le
    (show (cosetGraph R).dist d a ≤ 2 from ?_)
  · exact le_rfl
  have hd := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)
  have ht := SimpleGraph.dist_eq_one_iff_adj.mpr
    ((cosetGraph_adj R _ _).mpr (adjacent_symm R hat))
  have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := t) (w := a)
  omega

variable [Finite M]

theorem V_le_of_normalized_neighbor {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (K : Subgroup (FreeAmalgam R))
    (hn : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R)))
    (htK : V R t ≤ K) : V R a ≤ K := by
  have hneighbor (u : Vertex R) (hau : Adjacent R a u) : V R u ≤ K := by
    obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R a hat hau
    rw [← hgt, V_act]
    have hm := mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer R a).inv_mem hg))
    exact (map_mono htK).trans_eq hm
  apply Geometry.V_le_of_m_ball ha
  intro d hd hdist
  by_cases he : d = a
  · subst d
    have haV : Z R a ≤ V R t := by
      apply le_iSup_of_le a
      apply le_iSup_of_le (show (cosetGraph R).dist a t ≤ 2 by
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)]
        decide)
      exact le_rfl
    exact haV.trans htK
  have heven : Even ((cosetGraph R).dist d a) := by
    obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d a
    rw [← hw, walk_even_iff_color_eq, hd, ha]
  have hpos := (cosetGraph_connected R).pos_dist_of_ne he
  have htwo : (cosetGraph R).dist d a = 2 := by
    rw [Nat.even_iff] at heven
    omega
  obtain ⟨u, hdu, hau⟩ := exists_common_neighbor_of_dist_two R d a htwo
  have hdV : Z R d ≤ V R u := by
    apply le_iSup_of_le d
    apply le_iSup_of_le (show (cosetGraph R).dist d u ≤ 2 by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdu)]
      decide)
    exact le_rfl
  exact hdV.trans (hneighbor u hau)

theorem neighbor_centralizer_bound (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (bounds : BoundsAt geometry a) :
    ⁅V R a, Q R a ⊓ centralizer (V R t : Set (FreeAmalgam R))⁆ ≤
      fixedCore R a := by
  let K := Q R a ⊓ centralizer (V R t : Set (FreeAmalgam R))
  let C := commutatorPreimage (V R a) K (fixedCore R a)
  have hVG : V R a ≤ stabilizer R a :=
    (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hQG : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  have hDN := fixedCore_normalized (R := R) a
  have hCV : C ≤ V R a := commutatorPreimage_le _ _ _
  have hCK : ⁅C, K⁆ ≤ fixedCore R a :=
    commutator_commutatorPreimage_le _ _ _ (hVG.trans hDN)
  have hQnVt : Q R a ≤ normalizer (V R t : Set (FreeAmalgam R)) :=
    (show Q R a ≤ stabilizer R t from fun _ hx => hx.2 t hat).trans (V_normalized t)
  have hQnK : Q R a ≤ normalizer (K : Set (FreeAmalgam R)) :=
    (le_inf (Q R a).le_normalizer
      (hQnVt.trans (normalizer_le_normalizer_centralizer (V R t)))).trans
        inf_normalizer_le_normalizer_inf
  have hQnC : Q R a ≤ normalizer (C : Set (FreeAmalgam R)) :=
    commutatorPreimage_normalized _ _ _ _ (hVG.trans hDN)
      (hQG.trans (V_normalized a)) hQnK (hQG.trans hDN)
  have hLnC : Ltilde R a ≤ normalizer (C : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply le_commutatorPreimage
    · exact (commutator_mono le_rfl hCV).trans
        (le_normalizer_iff_commutator_le_right.mp
          ((Ltilde_le_stabilizer a).trans (V_normalized a)))
    · apply commutator_commutator_le_of_rotate_of_le_normalizer
        ((Ltilde_le_stabilizer a).trans hDN) ((hCV.trans hVG).trans hDN)
        ((show K ≤ Q R a from inf_le_left).trans (hQG.trans hDN))
      · exact (commutator_mono hCK le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer a).trans hDN))
      · rw [commutator_comm ⁅K, Ltilde R a⁆ C]
        exact (commutator_mono hCV (commutator_mono inf_le_left le_rfl)).trans
          bounds.triple
  have hGnC : stabilizer R a ≤ normalizer (C : Set (FreeAmalgam R)) := by
    rw [← source.local_generation a ha]
    exact sup_le hLnC hQnC
  have htC : V R t ≤ C := by
    apply le_commutatorPreimage (adjacent_V_le ha hat)
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (show K ≤ centralizer (V R t : Set (FreeAmalgam R)) from
        inf_le_right))).le.trans bot_le
  exact (commutator_mono (V_le_of_normalized_neighbor ha hat C hGnC htC) le_rfl).trans hCK

omit [Finite M] in
theorem FrontPath.start_Z_le_second_V {p : Counterexample geometry} (path : FrontPath p) :
    Z R p.a ≤ V R path.second :=
  le_iSup_of_le p.a (le_iSup_of_le path.start_second_distance.le le_rfl)

theorem FrontPath.predecessor_centralizes_third {p : Counterexample geometry}
    (path : FrontPath p) (ip : InitialFacts p) :
    V R p.c ≤ centralizer (V R path.third : Set (FreeAmalgam R)) := by
  have hrev := Geometry.before_reverse p.before
  have hdist := Geometry.before_distance (geometry := geometry) hrev path.third_before
    (show 3 ≤ (cosetGraph R).dist p.a p.a' - 2 by rw [p.distance_eq_b]; have := ip.six_le; omega)
  rw [p.distance_eq_b] at hdist
  apply le_centralizer_iff.mpr
  apply Geometry.V_le_of_h_neighbors path.second_color
    (adjacent_symm R path.third_second_adjacent)
  intro d hdt
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    cases hc : color R d <;> simp_all [path.third_color]
  have hVQ : V R p.c ≤ Q R d := by
    apply Geometry.V_le_Q_of_distance p.before_color
    have hone := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdt))
    have htri := (cosetGraph_connected R).dist_triangle
      (u := p.c) (v := path.third) (w := d)
    have := ip.six_le
    omega
  exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)).trans
    (centralizer_le hVQ)

/-- The second vertex of the original critical path cannot contain Z_alpha
in its fixed preimage: that would make Z_alpha Z_(alpha+2) normal, contrary
to the forward nonnormality theorem (2.2)(iv). -/
theorem FrontPath.start_moving_at_second (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    {p : Counterexample geometry} (path : FrontPath p) :
    p.a ∈ movingNeighbors geometry path.second := by
  refine ⟨path.second_before.1, ?_⟩
  have hnon := (critical_nonnormal_forward R geometry
    (source.adjacent_centralizer geometry.radical_ne_bot) p.a p.color_a
    (by rw [geometry.distance_constant p.a p.color_a]; exact lt_trans (by decide : 0 < 2) hb)
    p.a' p.critical path.second path.start_second_distance (by
      have hh := path.second_before.2
      rwa [SimpleGraph.dist_comm (u := p.a'), SimpleGraph.dist_comm (u := p.a')] at hh)).2
  rw [modules.X_eq_Z path.second path.second_color] at hnon
  intro hB
  apply hnon
  apply normal_subgroupOf_of_le_normalizer
  rw [← source.local_generation path.second path.second_color]
  apply sup_le
  · apply le_normalizer_iff.mpr
    intro l hl x hx
    have hm : (Z R p.a ⊔ Z R path.second).map (MulAut.conj l).toMonoidHom ≤
        Z R p.a ⊔ Z R path.second := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨y, hy, rfl⟩
        change l * y * l⁻¹ ∈ Z R p.a ⊔ Z R path.second
        have hc := ((mem_B_iff R path.second (geometry.Z_normal path.second)
          ((geometry.V_le_Q hb path.second path.second_color).trans
            (show Q R path.second ≤ stabilizer R path.second from fun _ hz => hz.1)) y).mp
              (hB hy)).2 l hl
        rw [show l * y * l⁻¹ = ⁅l, y⁆ * y by simp [commutatorElement_def, mul_assoc]]
        exact (Z R p.a ⊔ Z R path.second).mul_mem (mem_sup_right hc) (mem_sup_left hy)
      · rintro _ ⟨y, hy, rfl⟩
        exact mem_sup_right
          ((Z_normalized R path.second (Ltilde_le_stabilizer path.second hl) y).mp hy)
    exact hm (mem_map_of_mem (MulAut.conj l).toMonoidHom hx)
  · exact (le_inf
      ((Q_le_stabilizer_of_dist_two R path.second p.a path.second_color
        path.second_before.1).trans (Z_normalized R p.a))
      ((show Q R path.second ≤ stabilizer R path.second from fun _ hx => hx.1).trans
        (Z_normalized R path.second))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Transport the full natural section's triple commutator from the local
stabilizer into the amalgam; normality remains relative to the stabilizer. -/
theorem natural_section_triple (hb : 2 < geometry.b R)
    {a : Vertex R} (ha : color R a = false)
    (s : NaturalSectionAt a (V R a) (Z R a)) :
    ⁅⁅V R a, Q R a⁆, Ltilde R a⁆ ≤ Z R a := by
  have hQ : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  have hV : V R a ≤ stabilizer R a := (geometry.V_le_Q hb a ha).trans hQ
  have htriple := map_mono (f := (stabilizer R a).subtype) s.module_section.triple_le
  rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le hV,
    map_subgroupOf_eq_of_le hQ, map_subgroupOf_eq_of_le (Z_le_stabilizer R a)] at htriple
  exact htriple

/-- The triple-commutator clause in the full natural section places the
kernel displacement in the literal quotient-fixed preimage. -/
theorem commutator_le_fixed_preimage (hb : 2 < geometry.b R)
    {a : Vertex R} (ha : color R a = false)
    (s : NaturalSectionAt a (V R a) (Z R a)) :
    ⁅V R a, Q R a⁆ ≤ B R a (geometry.Z_normal a) := by
  have hQ : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  have hV : V R a ≤ stabilizer R a := (geometry.V_le_Q hb a ha).trans hQ
  have htriple := natural_section_triple hb ha s
  intro x hx
  apply (mem_B_iff R a (geometry.Z_normal a) hV x).mpr
  refine ⟨le_normalizer_iff_commutator_le_left.mp (hQ.trans (V_normalized a)) hx, ?_⟩
  intro l hl
  rw [commutator_comm] at htriple
  exact htriple (commutator_mem_commutator hl hx)

/-- If the kernel commutator of V/Z is fixed by the residual, it lies in
every incident radius layer. For W = V_t, the subgroup Z[W,Q] is normalized
by Q and by L. Its commutator preimage contains W and is normalized by the
whole vertex group, so neighbor generation makes it contain V. -/
theorem neighbor_radical_bound (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (s : NaturalSectionAt a (V R a) (Z R a)) :
    ⁅V R a, Q R a⁆ ≤ V R t := by
  let W := V R t
  let N := Z R a ⊔ ⁅W, Q R a⁆
  have hQG : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  have hVG : V R a ≤ stabilizer R a := (geometry.V_le_Q hb a ha).trans hQG
  have hWV : W ≤ V R a := adjacent_V_le ha hat
  have hZW : Z R a ≤ W := by
    apply le_iSup_of_le a
    apply le_iSup_of_le (show (cosetGraph R).dist a t ≤ 2 by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)]
      decide)
    exact le_rfl
  have hQW : Q R a ≤ normalizer (W : Set (FreeAmalgam R)) :=
    (show Q R a ≤ stabilizer R t from fun _ hx => hx.2 t hat).trans (V_normalized t)
  have hNW : N ≤ W := sup_le hZW (le_normalizer_iff_commutator_le_left.mp hQW)
  have hQN : Q R a ≤ normalizer (N : Set (FreeAmalgam R)) :=
    (le_inf (hQG.trans (Z_normalized R a)) (normalizer_commutator_ge_right W (Q R a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hNL : ⁅N, Ltilde R a⁆ ≤ Z R a := by
    let P := commutatorPreimage (stabilizer R a) (Ltilde R a) (Z R a)
    have hZP : Z R a ≤ P := le_commutatorPreimage (Z_le_stabilizer R a)
      (le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer a).trans (Z_normalized R a)))
    have hWP : ⁅W, Q R a⁆ ≤ P := by
      apply le_commutatorPreimage
        ((le_normalizer_iff_commutator_le_left.mp hQW).trans (hWV.trans hVG))
      exact (commutator_mono (commutator_mono hWV le_rfl) le_rfl).trans
        (natural_section_triple hb ha s)
    exact (commutator_mono (sup_le hZP hWP) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ (Z_normalized R a))
  have hLN : Ltilde R a ≤ normalizer (N : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr (hNL.trans le_sup_left)
  have hGN : stabilizer R a ≤ normalizer (N : Set (FreeAmalgam R)) := by
    rw [← source.local_generation a ha]
    exact sup_le hLN hQN
  let C := commutatorPreimage (V R a) (Q R a) N
  have hGC : stabilizer R a ≤ normalizer (C : Set (FreeAmalgam R)) :=
    commutatorPreimage_normalized _ _ _ _ (hVG.trans hGN)
      (V_normalized a) (Q_normalized R a) hGN
  have hWC : W ≤ C := le_commutatorPreimage hWV le_sup_right
  exact ((commutator_mono (V_le_of_normalized_neighbor ha hat C hGC hWC) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (hVG.trans hGN))).trans hNW

/-- Universal initial facts give the full natural section at the original
second path vertex, without identifying a transported critical geodesic. -/
theorem FrontPath.start_commutator_le_fixed_preimage (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    {p : Counterexample geometry}
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) (path : FrontPath p) :
    ⁅Z R p.a, Q R path.second⁆ ≤ B R path.second (geometry.Z_normal path.second) := by
  obtain ⟨q, hqa, _⟩ := contrary_at p bad path.second path.second_color
  obtain ⟨iq⟩ := initial q
  have s : NaturalSectionAt path.second (V R path.second) (Z R path.second) := by
    simpa only [hqa] using iq.natural_section
  exact (commutator_mono path.start_Z_le_second_V le_rfl).trans
    (commutator_le_fixed_preimage hb path.second_color s)

/-- The transported (4.3.1)(vii) identity applies at the original second
vertex because forward nonnormality proves the moving condition. -/
theorem FrontPath.edge_eq_second_commutator (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    {p : Counterexample geometry}
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) (path : FrontPath p) :
    edgeDisplacement p.a path.first = ⁅Z R p.a, Q R path.second⁆ :=
  (StepThree.moving_commutator_eq_edge_at p (by omega) initial bad
    path.second path.first p.a path.second_color path.second_first_adjacent
    path.start_first_adjacent (path.start_moving_at_second source hb modules)).symm

/-- The edge displacement lies in the literal fixed preimage at alpha+2. -/
theorem FrontPath.edge_le_fixed_preimage (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    {p : Counterexample geometry}
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) (path : FrontPath p) :
    edgeDisplacement p.a path.first ≤ B R path.second (geometry.Z_normal path.second) := by
  rw [path.edge_eq_second_commutator source hb modules initial bad]
  exact path.start_commutator_le_fixed_preimage hb initial bad

/-- The missing path placement uses the radical bound in the actual
natural section at alpha+2, not a containment inferred from distance alone. -/
theorem FrontPath.edge_le_third_V (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    {p : Counterexample geometry}
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) (path : FrontPath p) :
    edgeDisplacement p.a path.first ≤ V R path.third := by
  obtain ⟨q, hqa, _⟩ := contrary_at p bad path.second path.second_color
  obtain ⟨iq⟩ := initial q
  have s : NaturalSectionAt path.second (V R path.second) (Z R path.second) := by
    simpa only [hqa] using iq.natural_section
  rw [path.edge_eq_second_commutator source hb modules initial bad]
  exact (commutator_mono path.start_Z_le_second_V le_rfl).trans
    (neighbor_radical_bound source hb path.second_color
      (adjacent_symm R path.third_second_adjacent) s)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
