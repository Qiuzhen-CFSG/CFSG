module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Geometry

/-!
# Selecting the three generating Z-layers

This constructs the delta chosen in the proof of MS93 (4.5.4)(iii), with its
actual transporter in G_c and on the supplied source path. The only retained
early-layer premise is the translated (4.5.3)(i) equality at c; its producer
is the early-layer assembly, `qt-c01-ms93-core-factors-early-layers`.

The unequal edge layers at positions five and seven are distinct subgroups
of index two in Z_c. They generate Z_c inside Z_a Z_d. The critical windows
at positions four and zero, the latter reversed, show respectively that
Z_a is not contained in Z_c and Z_d is not contained in Z_c Z_a. Thus these
two subgroups already give index at least four over Z_c. The genuine natural
section from `Earlier` bounds the whole first hat layer's index by eight.
The turn at c identifies the Z_a and Z_d orbit spans. If the first two
subgroups do not generate, any conjugate escaping their join finishes the
index-eight group and supplies the required transporter.

All product-to-join conversions take place inside the elementary radius-two
group V_c. `exists_generating_factors` consumes the literal preceding product
and applies `DeltaChoice.factors_generate` to the newly constructed choice.
The same choice remains available for (4.5.4)(iv). Recognition of the two
quotient factors and final source assembly are separate obligations.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), standing convention and (4.5.3)(i), pp.895--898; selection in the
proof of (4.5.4)(iii), printed p.899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Selection
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

private theorem radius_commutator_le_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (ha : color R a = false) : ⁅V R a, Q R a⁆ ≤ Z R a := by
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

/-- The genuine preceding natural section bounds the first hat quotient.
Only the literal equality (4.5.3)(i) is an additional source input. -/
private theorem hatV_relIndex_le_eight_at (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c : Vertex R} (ha : color R a = false)
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a) :
    (Z R a).relIndex (hatV R a c) ≤ 8 := by
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
  exact (relIndex_le_of_le_right hle (by rw [hsize]; decide)).trans hsize.le


private theorem index_ge_two_of_not_le {G : Type*} [Group G]
    {A B : Subgroup G} [Finite B] (h : ¬ B ≤ A) : 2 ≤ A.relIndex B := by
  have hp : 0 < A.relIndex B :=
    Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := A.subgroupOf B))
  have hn : A.relIndex B ≠ 1 := fun he => h (relIndex_eq_one.mp he)
  omega

private theorem join_eq_of_distinct_index_two {G : Type*} [Group G]
    {A B N : Subgroup G} (hA : A ≤ N) (hB : B ≤ N)
    (hiA : A.relIndex N = 2) (hiB : B.relIndex N = 2) (hne : A ≠ B) : A ⊔ B = N := by
  have hPN : A ⊔ B ≤ N := sup_le hA hB
  have hnot : ¬ A ⊔ B ≤ A := by
    intro h
    have hBA := le_sup_right.trans h
    have hm := relIndex_mul_relIndex B A N hBA hA
    rw [hiA, hiB] at hm
    exact hne (le_antisymm (relIndex_eq_one.mp (by omega)) hBA)
  have hmul := relIndex_mul_relIndex A (A ⊔ B) N le_sup_left hPN
  rw [hiA] at hmul
  have hdiv : (A ⊔ B).relIndex N ∣ 2 :=
    ⟨A.relIndex (A ⊔ B), by simpa only [Nat.mul_comm] using hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
  · exact le_antisymm hPN (relIndex_eq_one.mp h)
  · rw [h] at hmul
    exact False.elim (hnot (relIndex_eq_one.mp (by omega)))

private theorem third_conjugate_generates {G : Type*} [Group G]
    {A B N H S : Subgroup G} [Finite H]
    (hspan : H = conjugatesIn A S) (hA : A ≤ H) (hB : B ≤ H)
    (hNP : N ≤ A ⊔ B) (hAN : ¬ A ≤ N) (hBNA : ¬ B ≤ N ⊔ A)
    (hindex : N.relIndex H ≤ 8) :
    ∃ g : S, H = A ⊔ rightConjugate A g ⊔ B := by
  let P := A ⊔ B
  let T := N ⊔ A
  have hTP : T ≤ P := sup_le hNP le_sup_left
  have hPH : P ≤ H := sup_le hA hB
  let : Finite P := Finite.of_injective (inclusion hPH) (inclusion_injective _)
  let : Finite T := Finite.of_injective (inclusion (hTP.trans hPH)) (inclusion_injective _)
  by_cases he : P = H
  · refine ⟨1, ?_⟩
    have hconj : rightConjugate A (1 : G) = A := by
      ext x
      simp [rightConjugate]
    simpa only [Subgroup.coe_one, hconj, sup_idem] using he.symm
  have hnot : ¬ conjugatesIn A S ≤ P := by
    rw [← hspan]
    exact fun h => he (le_antisymm hPH h)
  obtain ⟨g, hg⟩ : ∃ g : S, ¬ rightConjugate A g ≤ P := by
    simpa only [conjugatesIn, iSup_le_iff, not_forall] using hnot
  let K := P ⊔ rightConjugate A g
  have hKH : K ≤ H := sup_le hPH (hspan ▸ le_iSup (fun k : S => rightConjugate A k) g)
  let : Finite K := Finite.of_injective (inclusion hKH) (inclusion_injective _)
  have hNT : 2 ≤ N.relIndex T := index_ge_two_of_not_le
    (fun h => hAN (le_sup_right.trans h))
  have hTPi : 2 ≤ T.relIndex P := index_ge_two_of_not_le
    (fun h => hBNA (le_sup_right.trans h))
  have hPK : 2 ≤ P.relIndex K := index_ge_two_of_not_le
    (fun h => hg (le_sup_right.trans h))
  have hm₁ := relIndex_mul_relIndex N T P le_sup_left hTP
  have hm₂ := relIndex_mul_relIndex N P K hNP le_sup_left
  have hm₃ := relIndex_mul_relIndex N K H (hNP.trans le_sup_left) hKH
  have hNPi : 4 ≤ N.relIndex P := by nlinarith
  have hNKi : 8 ≤ N.relIndex K := by nlinarith
  have hp : 0 < K.relIndex H :=
    Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := K.subgroupOf H))
  have hKi : K.relIndex H = 1 := by nlinarith
  have hKH' : K = H := le_antisymm hKH (relIndex_eq_one.mp hKi)
  refine ⟨g, ?_⟩
  calc
    H = (A ⊔ B) ⊔ rightConjugate A g := hKH'.symm
    _ = A ⊔ rightConjugate A g ⊔ B := by ac_rfl

private theorem path_color (p : Higher.SourcePath (alpha R))
    {i : ℕ} (hi : Even i) (hle : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; exact hle)).mpr hi

private theorem path_adjacent (p : Higher.SourcePath (alpha R))
    {i : ℕ} (hi : i < 14) : Adjacent R (p.walk.getVert i) (p.walk.getVert (i + 1)) :=
  (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by rw [p.length_eq]; exact hi))

private theorem near_Z_le_Q (earlier : Earlier R geometry) {a b : Vertex R}
    (ha : color R a = false) (hd : (cosetGraph R).dist a b < 8) : Z R a ≤ Q R b :=
  Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    (by
      rw [(geometry.distance_constant a ha).trans earlier.distance]
      exact hd)

/-- The actual source delta, conditional only on the translated (4.5.3)(i). -/
theorem exists_deltaChoice [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6)) :
    Nonempty (DeltaChoice p) := by
  let a := alpha R
  let c := p.walk.getVert 6
  let d := p.walk.getVert 8
  let H := hatV R c d
  have hc : color R c = false := path_color p (by decide) (by decide)
  have hd : color R d = false := path_color p (by decide) (by decide)
  have h0 : color R (p.walk.getVert 0) = false := path_color p (by decide) (by decide)
  have hadj : Adjacent R a (p.walk.getVert 5) := by
    simpa only [p.center_eq] using path_adjacent p (i := 4) (by decide)
  have hc5 : Adjacent R c (p.walk.getVert 5) :=
    adjacent_symm R (path_adjacent p (i := 5) (by decide))
  have hc7 : Adjacent R c (p.walk.getVert 7) := path_adjacent p (i := 6) (by decide)
  have hd7 : Adjacent R d (p.walk.getVert 7) :=
    adjacent_symm R (path_adjacent p (i := 7) (by decide))
  have h5c := Escape.EdgeTransfer.edge_Z_le c _ hc hc5
  have h7c := Escape.EdgeTransfer.edge_Z_le c _ hc hc7
  have hZc : Z R (p.walk.getVert 5) ⊔ Z R (p.walk.getVert 7) = Z R c :=
    join_eq_of_distinct_index_two h5c h7c
      (earlier.edge_Z_index c _ hc hc5) (earlier.edge_Z_index c _ hc hc7)
      (p.distinct_Z 6 (by decide) (by decide) (by decide))
  have hNP : Z R c ≤ Z R a ⊔ Z R d := by
    rw [← hZc]
    exact sup_le_sup (Escape.EdgeTransfer.edge_Z_le a _ rfl hadj)
      (Escape.EdgeTransfer.edge_Z_le d _ hd hd7)
  have hAN : ¬ Z R a ≤ Z R c := by
    intro h
    apply (p.critical 4 (by decide) (by decide)).2
    rw [p.center_eq]
    exact h.trans (near_Z_le_Q earlier hc (by
      rw [p.dist (i := 6) (j := 12) (by decide) (by decide)]; decide))
  have hcrit : CriticalPair R (p.walk.getVert 0) d (geometry.exists_critical _ h0) := by
    refine ⟨?_, (p.critical 0 (by decide) (by decide)).2⟩
    rw [(geometry.distance_constant _ h0).trans earlier.distance]
    exact p.dist (i := 0) (j := 8) (by decide) (by decide)
  have hreverse := common.critical_reverse _ h0 _ hd hcrit
  have hBNA : ¬ Z R d ≤ Z R c ⊔ Z R a := by
    intro h
    apply hreverse.2
    apply h.trans
    apply sup_le
    · exact near_Z_le_Q earlier hc (by
        rw [SimpleGraph.dist_comm, p.dist (i := 0) (j := 6) (by decide) (by decide)]; decide)
    · exact near_Z_le_Q earlier rfl (by
        change (cosetGraph R).dist (alpha R) (p.walk.getVert 0) < 8
        have hh := p.dist (i := 0) (j := 4) (by decide) (by decide)
        rw [p.center_eq] at hh
        rw [SimpleGraph.dist_comm, hh]; decide)
  obtain ⟨g, hg, ht⟩ := p.turns 6 (by decide) (by decide) (by decide)
  have he : hatV R c a = H := by
    change localZSpan R a c = localZSpan R d c
    have ht' : act R g d = a := by simpa only [p.center_eq] using ht
    rw [← ht']
    exact LocalCommutator.CriticalCase.span_eq_of_local_conjugator hg
  have hspan : H = conjugatesIn (Z R a) (stabilizer R c) :=
    he.symm.trans (hatV_eq_conjugatesIn R c a)
  have hAH : Z R a ≤ H := by
    rw [hspan]
    exact Escape.Initial.Natural.conjugatesIn_contains _ _
  have hBH : Z R d ≤ H := Z_le_localZSpan R d c
  have hHlocal : H ≤ stabilizer R c :=
    (hatV_le_radius R p.two_step_distances.2.1.le).trans
      (geometry.V_local c hc (by rw [(geometry.distance_constant c hc).trans earlier.distance]; decide))
  let : Finite (stabilizer R c) := finite_stabilizer R c
  let : Finite H := Finite.of_injective (inclusion hHlocal) (inclusion_injective _)
  obtain ⟨k, hk⟩ := third_conjugate_generates hspan hAH hBH hNP hAN hBNA
    (hatV_relIndex_le_eight_at common earlier hc hVc)
  refine ⟨{ vertex := act R k a, transporter := k, vertex_eq := rfl, generation := ?_ }⟩
  simpa only [rightConjugate, ← Z_act] using hk

private theorem sup_product_of_abelian_overgroup {G : Type*} [Group G]
    {A B H : Subgroup G} [IsMulCommutative H] (hA : A ≤ H) (hB : B ≤ H) :
    ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) := by
  apply coe_mul_of_left_le_normalizer_right
  exact (hA.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans
    ((centralizer_le hB).trans (Subgroup.centralizer_le_normalizer _))

/-- The source product is a literal setwise product in the elementary radius-two group. -/
theorem generation_product (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p) :
    (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) =
      (Z R (alpha R) : Set (FreeAmalgam R)) * (Z R δ.vertex : Set (FreeAmalgam R)) *
        (Z R (p.walk.getVert 8) : Set (FreeAmalgam R)) := by
  let c := p.walk.getVert 6
  have hc : color R c = false := path_color p (by decide) (by decide)
  let := PathCentrality.V_elementary_of_four_lt R hc (by rw [earlier.distance]; decide)
  have hh : Z R (alpha R) ⊔ Z R δ.vertex ⊔ Z R (p.walk.getVert 8) ≤ V R c :=
    δ.generation.ge.trans (hatV_le_radius R p.two_step_distances.2.1.le)
  have hpair : Z R (alpha R) ⊔ Z R δ.vertex ≤ V R c := le_sup_left.trans hh
  rw [δ.generation, sup_product_of_abelian_overgroup hpair (le_sup_right.trans hh),
    sup_product_of_abelian_overgroup (le_sup_left.trans hpair) (le_sup_right.trans hpair)]

/-- Apply the newly selected delta to the actual two orbit factors of (4.5.4)(iii).
The only retained early-layer premise is (4.5.3)(i) at c, produced by the
separate early-layer assembly. -/
theorem exists_generating_factors [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVc : (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) =
      (Vcirc R (p.walk.getVert 6) : Set (FreeAmalgam R)) *
        (Z R (p.walk.getVert 6) : Set (FreeAmalgam R))) :
    ∃ δ : DeltaChoice p,
      orbitFactor p (p.walk.getVert 8) ⊔ orbitFactor p δ.vertex =
        hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ∧
      (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Z R (alpha R) : Set (FreeAmalgam R)) * (Z R δ.vertex : Set (FreeAmalgam R)) *
          (Z R (p.walk.getVert 8) : Set (FreeAmalgam R)) := by
  have hc : color R (p.walk.getVert 6) = false := path_color p (by decide) (by decide)
  let := PathCentrality.V_elementary_of_four_lt R hc (by rw [earlier.distance]; decide)
  have hjoin : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6) := by
    apply SetLike.coe_injective
    rw [sup_product_of_abelian_overgroup (DistanceEight.Vcirc_le_V R _)
      (Z_le_VBall R (p.walk.getVert 6) 2)]
    exact hVc
  obtain ⟨δ⟩ := exists_deltaChoice common earlier p hjoin
  exact ⟨δ, δ.factors_generate, generation_product earlier δ⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Selection
