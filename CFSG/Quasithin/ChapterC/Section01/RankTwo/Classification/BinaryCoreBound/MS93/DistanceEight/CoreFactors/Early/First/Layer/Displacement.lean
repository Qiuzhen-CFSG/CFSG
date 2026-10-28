module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Calculations
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Bounds
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
/-!
# Edge displacement and the second orbit layer

The two edge indices in `Earlier` give displacement of order four. Distance
places the second orbit layer in the midpoint kernel and makes the radius
at the preceding edge centralize it. Moving/edge generation then bounds
its displacement by the midpoint H. Thus the literal product in (4.5.1)(iv)
implies the lower bound in (v).

The product itself is proved here only from an explicit strict image bound.
Recovering that bound requires the two independent displacements chosen in
the final calculation of (4.4); it is not asserted by this module.
All normalizers and indices refer to the actual subgroups of the amalgam.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.895--896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Layer
open PathCentrality PathCentrality.LocalCommutator
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The two preceding edge indices identify the faithful edge action with its displacement of order four. -/
theorem edge_displacement_card (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {d t : Vertex R}
    (hd : color R d = false) (hdt : Adjacent R d t) :
    Nat.card (⁅Z R d, Q R t⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  have hn : Q R t ≤ stabilizer R d := fun _ hx => hx.2 d (adjacent_symm R hdt)
  have he := Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (moduleFacts common) d t hd hdt
  have hc : ⁅Z R d, Q R t⁆ ≤ Z R t :=
    commutator_le_of_normalized_index_two _ _ _ (Escape.EdgeTransfer.edge_Z_le d t hd hdt)
      (earlier.edge_Z_index d t hd hdt) (hn.trans (Z_normalized R d))
      ((show Q R t ≤ stabilizer R t from fun _ hx => hx.1).trans (Z_normalized R t))
  let := geometry.Z_elementary (by have := common.large_distance; omega) d hd
  have hi := DistanceFour.Early.actor_index_eq_displacement_card_of_fixed_index_two
    (Z R d) (Q R t) (hn.trans (Z_normalized R d))
    (hc.trans (he ▸ inf_le_right)) (he ▸ earlier.edge_Z_index d t hd hdt)
  have hk : (centralizer (Z R d : Set (FreeAmalgam R))).relIndex (Q R t) =
      (Q R d).relIndex (Q R t) := by
    rw [← inf_relIndex_right, inf_comm, common.centralizer d t hd hdt]
  rw [hk, earlier.edge_Q_index d t hd hdt] at hi
  exact hi.symm

omit [Finite M] in
/-- Radius four at a lies in the edge kernel three steps along the path. -/
theorem hatW_le_edge_kernel (earlier : Earlier R geometry)
    {a c d t : Vertex R} (ha : color R a = false)
    (hca : (cosetGraph R).dist c a ≤ 2) (hdc : (cosetGraph R).dist d c ≤ 2)
    (hat : (cosetGraph R).dist a t = 3) : hatW R a c d ≤ Q R t := by
  apply (hatW_le_radius R hca hdc).trans
  apply (Escape.Propagation.RadiusFour.Forward.VBall_le_iff ha _).mpr
  intro x hx hxa
  apply Z_le_Q_of_dist_lt R x (geometry.exists_critical x hx)
  rw [geometry.distance_constant x hx]
  change (cosetGraph R).dist x t < geometry.b R
  have htri := (cosetGraph_connected R).dist_triangle (u := x) (v := a) (w := t)
  rw [earlier.distance]
  omega

omit [Finite M] in
/-- The second orbit layer lies in the two-core at its midpoint. -/
theorem hatW_le_middle_kernel (earlier : Earlier R geometry)
    {a c d : Vertex R} (hc : color R c = false)
    (hca : (cosetGraph R).dist c a ≤ 2) (hdc : (cosetGraph R).dist d c ≤ 2) :
    hatW R a c d ≤ Q R c := by
  apply (hatW_le_radius R hca hdc).trans
  apply (Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le c a 4 6 ?_).trans
    (Escape.Propagation.RadiusFour.VBall_le_Q c hc 6 (by rw [earlier.distance]; decide))
  rw [SimpleGraph.dist_comm]
  omega

omit [Finite M] in
private theorem H_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (H R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅Vcirc R a, Q R a⁆ : Subgroup (FreeAmalgam R)).map _ = _
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (Vcirc_normalized a hg),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hg)]
  rfl

omit [Finite M] in
/-- The radius at the first path edge centralizes the second orbit layer. -/
theorem edgeRadius_centralizes_hatW (earlier : Earlier R geometry)
    {a c d s : Vertex R} (hc : color R c = false) (hcs : Adjacent R c s)
    (hca : (cosetGraph R).dist c a ≤ 2) (hdc : (cosetGraph R).dist d c ≤ 2)
    (has : (cosetGraph R).dist a s = 1) :
    ⁅V R s, hatW R a c d⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply Escape.Initial.Consequences.V_le_of_h_neighbors hc hcs
  intro u hus
  have hu : color R u = false := by
    have h₁ := adjacent_color_ne R hcs
    have h₂ := adjacent_color_ne R hus
    cases h : color R u <;> cases h' : color R s <;> simp_all
  have hdist : (cosetGraph R).dist a u ≤ 2 := by
    have hsu := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (adjacent_symm R hus))
    have hh := (cosetGraph_connected R).dist_triangle (u := a) (v := s) (w := u)
    omega
  have hWQ : hatW R a c d ≤ Q R u :=
    (hatW_le_radius R hca hdc).trans
      ((Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le u a 4 6 (by omega)).trans
        (Escape.Propagation.RadiusFour.VBall_le_Q u hu 6 (by rw [earlier.distance]; decide)))
  exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes u hu)).trans
    (centralizer_le hWQ)

/-- The displacement in the final display on p.896 lies in H at the midpoint, before using the product identity. -/
theorem hatW_displacement_le_H (source : LocalSource L R)
    (earlier : Earlier R geometry) {a c d s : Vertex R}
    (hc : color R c = false) (hcs : Adjacent R c s)
    (hca : (cosetGraph R).dist c a ≤ 2) (hdc : (cosetGraph R).dist d c ≤ 2)
    (has : (cosetGraph R).dist a s = 1) :
    ⁅Z R d, hatW R a c d⁆ ≤ H R c := by
  have hWQ := hatW_le_middle_kernel earlier hc hca hdc
  have hVQ := geometry.V_le_Q (by rw [earlier.distance]; decide) c hc
  have hVW : V R c ≤ commutatorPreimage (Q R c) (hatW R a c d) (H R c) := by
    rw [Escape.Initial.Consequences.radius_eq_moving_sup_edge source hc hcs]
    apply sup_le
    · exact le_commutatorPreimage ((DistanceEight.Vcirc_le_V R c).trans hVQ)
        (commutator_mono le_rfl hWQ)
    · exact le_commutatorPreimage
        ((Escape.Initial.Consequences.edge_radius_le_radius hc hcs).trans hVQ)
        ((edgeRadius_centralizes_hatW earlier hc hcs hca hdc has).le.trans bot_le)
  have hZV : Z R d ≤ V R c := le_iSup_of_le d (le_iSup_of_le hdc le_rfl)
  exact (commutator_mono (hZV.trans hVW) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _
      ((show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (H_normalized c)))


/-- The literal source product implies the lower bound at the midpoint, using the actual order-four edge displacement. -/
theorem four_le_H_of_product (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a c d s t : Vertex R} (hc : color R c = false) (hd : color R d = false)
    (hcs : Adjacent R c s) (hdt : Adjacent R d t)
    (hca : (cosetGraph R).dist c a ≤ 2) (hdc : (cosetGraph R).dist d c ≤ 2)
    (has : (cosetGraph R).dist a s = 1)
    (hprod : (hatW R a c d : Set (FreeAmalgam R)) * (Q R d : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R))) : 4 ≤ Nat.card (H R c) := by
  have hW : hatW R a c d ≤ Q R t := by
    intro x hx
    have hx' : x ∈ (hatW R a c d : Set (FreeAmalgam R)) * (Q R d : Set (FreeAmalgam R)) :=
      ⟨x, hx, 1, (Q R d).one_mem, mul_one x⟩
    rwa [hprod] at hx'
  have hlocal : Q R t ≤ stabilizer R d := fun _ hx => hx.2 d (adjacent_symm R hdt)
  have hjoin : Q R d ⊔ hatW R a c d = Q R t := by
    apply SetLike.coe_injective
    rw [sup_comm, coe_mul_of_left_le_normalizer_right _ _
      (hW.trans (hlocal.trans (Q_normalized R d)))]
    exact hprod
  have he := commutator_eq_of_centralizing_sup hjoin
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)))
    (hW.trans (hlocal.trans (Z_normalized R d)))
  have hdisp : ⁅Z R d, Q R t⁆ ≤ H R c :=
    he ▸ hatW_displacement_le_H source earlier hc hcs hca hdc has
  let := finite_stabilizer R c
  let : Finite (H R c) := Finite.of_injective
    (inclusion ((H_le_Z_of_central common hc (earlier.centrality c hc)).trans (Z_le_stabilizer R c)))
    (inclusion_injective _)
  simpa only [edge_displacement_card common earlier hd hdt] using card_le_of_le hdisp

/-- An image larger than two fills the edge quotient of order four and gives the literal setwise product. -/
theorem hatW_product_of_large_image (earlier : Earlier R geometry)
    {a c d t : Vertex R} (ha : color R a = false) (hd : color R d = false)
    (hdt : Adjacent R d t)
    (hca : (cosetGraph R).dist c a ≤ 2) (hdc : (cosetGraph R).dist d c ≤ 2)
    (hat : (cosetGraph R).dist a t = 3)
    (himage : 2 < (Q R d).relIndex (hatW R a c d)) :
    (hatW R a c d : Set (FreeAmalgam R)) * (Q R d : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)) := by
  have hW := hatW_le_edge_kernel earlier ha hca hdc hat
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hdt
    cases h : color R t <;> simp_all
  have hQ : Q R d ≤ Q R t := Q_le_adjacent_h R ht hdt
  have hn : Q R t ≤ normalizer (Q R d : Set (FreeAmalgam R)) :=
    (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)).trans
      (Q_normalized R d)
  let A := (hatW R a c d).subgroupOf (Q R t)
  let K := (Q R d).subgroupOf (Q R t)
  let : K.Normal := normal_subgroupOf_of_le_normalizer hn
  have hi : K.relIndex A = 4 := by
    have hKi : K.index = 4 := earlier.edge_Q_index d t hd hdt
    have hdvd : K.relIndex A ∣ 4 := hKi ▸ K.relIndex_dvd_index_of_normal A
    have hh := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 4 ≠ 0)⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    have hgt : 2 < K.relIndex A := by rwa [relIndex_subgroupOf hW]
    omega
  have hm := relIndex_mul_index (show K ≤ A ⊔ K from le_sup_right)
  rw [relIndex_sup_right, hi, show K.index = 4 from earlier.edge_Q_index d t hd hdt] at hm
  have he : A ⊔ K = ⊤ := index_eq_one.mp (by omega)
  have hj : hatW R a c d ⊔ Q R d = Q R t := by
    have hh := congrArg (Subgroup.map (Q R t).subtype) he
    simpa only [A, K, Subgroup.map_sup, map_subgroupOf_eq_of_le hW,
      map_subgroupOf_eq_of_le hQ, ← MonoidHom.range_eq_map, range_subtype] using hh
  rw [← coe_mul_of_left_le_normalizer_right _ _ (hW.trans hn), hj]


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Layer
