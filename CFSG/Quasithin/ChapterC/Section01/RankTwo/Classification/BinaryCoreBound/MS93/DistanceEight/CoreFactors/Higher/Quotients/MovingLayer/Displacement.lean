module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.SourceAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.SourceRecognition

public import Theory.GroupAction.FixedCoatomDisplacement

/-!
# The source small actor on the moving orbit quotient

The central commutator line has order two. The adjacent fixed plane then
bounds the image of X modulo the neighboring two-core by two. The literal
earlier product writes that kernel inside hat W times the forward core;
the actual forward second layer fixes it modulo hat W. Thus the forward
actor fixes a subgroup of index at most two in X/hat W.

The original edge product gives this actor an order-four matrix image.
An involution in that image has displacement at most two. Together with
the previously constructed faithful action, small-involution recognition
constructs the intrinsic fixed and three-dimensional moving summands.
The marking has not yet been compared with CommonFacts.natural.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iv), p.899,
from its opening commutator bound through the assertion c(X)=1.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The first source estimate on p.899, before taking a quotient. -/
theorem moving_orbit_commutator_le_line (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅orbitMovingGroup (Early.Orbit.SourceApplications.higherPath geometry p),
      Z R (p.walk.getVert 6)⁆ ≤ H R (alpha R) ⊓ H R (p.walk.getVert 8) := by
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  let P := stabilizer R (alpha R)
  let C := H R (alpha R) ⊓ H R (p.walk.getVert 8)
  have hC : C ≤ (center P).map P.subtype :=
    inf_le_left.trans (H_le_localCenter_of_central R (alpha R) (earlier.centrality _ rfl))
  have hCZ : C ≤ centralizer (P : Set (FreeAmalgam R)) := by
    rintro x hx y hy
    obtain ⟨z,hz,rfl⟩ := hC hx
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y,hy⟩)
  have hN : P ≤ normalizer C := (le_centralizer_iff.mp hCZ).trans (Subgroup.centralizer_le_normalizer _)
  let D := commutatorPreimage P (Z R (p.walk.getVert 6)) C
  have hX : orbitMovingGroup q ≤ D := by
    apply sup_le
    · apply le_commutatorPreimage
      · exact (show conjugatesIn (hatV R (p.walk.getVert 8) (p.walk.getVert 10)) P ≤
          orbitMovingGroup q from le_sup_left).trans
          ((orbitMovingGroup_le_Q earlier q).trans (fun _ hx => hx.1))
      · rw [commutator_comm]
        have hZ : Z R (p.walk.getVert 6) ≤ V R (alpha R) :=
          (PathCentrality.Z_le_localZSpan R _ _).trans
            (hatV_le_radius R q.two_step_distances.1.le)
        have hV : hatV R (p.walk.getVert 8) (p.walk.getVert 10) ≤ V R (p.walk.getVert 8) :=
          hatV_le_radius R q.two_step_distances.2.2.le
        have hc := radius_orbit_commutator earlier (show color R (alpha R) = false from rfl)
          (p.even_color (i := 8) (by decide) (by decide))
          (show (cosetGraph R).dist (p.walk.getVert 8) (alpha R) ≤ 4 from by
            rw [SimpleGraph.dist_comm]
            simpa only [p.center_eq] using
              (p.distance (geometry := geometry) (i := 4) (j := 8) (by decide) (by decide)).le)
          (show ⁅V R (alpha R),V R (p.walk.getVert 8)⁆ = C from by
            simpa only [p.center_eq] using
              ((Early.firstFactsOnPath source common earlier p).forward 4
                (by decide) (by decide) (by decide)).commutator_eq)
        exact (commutator_mono hZ (iSup_mono fun _ => map_mono hV)).trans hc.le
    · apply le_commutatorPreimage
      · exact (show hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ≤
          orbitMovingGroup q from le_sup_right).trans
          ((orbitMovingGroup_le_Q earlier q).trans (fun _ hx => hx.1))
      · have hz : ⁅Z R (p.walk.getVert 6),
            hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ = ⊥ :=
          commutator_eq_bot_iff_le_centralizer.mpr
            ((PathCentrality.Z_le_localZSpan R _ _).trans
              (SecondLayer.Recognition.denominator_centralizes_second earlier q))
        rw [commutator_comm]
        change ⁅Z R (p.walk.getVert 6),hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ ≤ C
        rw [hz]
        exact bot_le
  exact (commutator_mono hX le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hN)

/-- The neighboring two-core has index at most two in the actual X. -/
theorem moving_orbit_neighbor_index_le_two (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (Q R (p.walk.getVert 6)).relIndex
      (orbitMovingGroup (Early.Orbit.SourceApplications.higherPath geometry p)) ≤ 2 := by
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  let A := orbitMovingGroup q
  let U := Z R (p.walk.getVert 6)
  let F := U ⊓ centralizer (A : Set (FreeAmalgam R))
  have hc := p.even_color (i := 6) (by decide) (by decide)
  have hat : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using p.adjacent (i := 4) (by decide)
  have hct : Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) :=
    adjacent_symm R (p.adjacent (i := 5) (by decide))
  have ht : color R (p.walk.getVert 5) = true := by
    have hn := adjacent_color_ne R hat
    change false ≠ _ at hn
    cases h : color R (p.walk.getVert 5) <;> simp_all
  have hAT : A ≤ Q R (p.walk.getVert 5) :=
    (orbitMovingGroup_le_Q earlier q).trans (Q_le_adjacent_h R ht hat)
  have hAG : A ≤ stabilizer R (p.walk.getVert 6) :=
    hAT.trans (fun _ hx => hx.2 _ (adjacent_symm R hct))
  have hk : (Q R (p.walk.getVert 6)).subgroupOf A =
      (centralizer (U : Set (FreeAmalgam R))).subgroupOf A := by
    ext x
    have hx := hAT x.property
    change (x : FreeAmalgam R) ∈ Q R (p.walk.getVert 6) ↔ _
    rw [← common.centralizer _ _ hc hct, mem_inf]
    exact and_iff_right hx
  change ((Q R (p.walk.getVert 6)).subgroupOf A).index ≤ 2
  rw [hk]
  change (centralizer (U : Set (FreeAmalgam R))).relIndex A ≤ 2
  by_cases hfix : F.relIndex U = 1
  · have hUA : U ≤ centralizer (A : Set (FreeAmalgam R)) :=
      (relIndex_eq_one.mp hfix).trans inf_le_right
    rw [relIndex_eq_one.mpr (le_centralizer_iff.mp hUA)]
    decide
  let := finite_stabilizer R (p.walk.getVert 6)
  let : Finite U := Finite.of_injective (inclusion (Z_le_stabilizer R _)) (inclusion_injective _)
  let : IsElementaryAbelian 2 U := geometry.Z_elementary (by rw [earlier.distance]; decide) _ hc
  have hZF : Z R (p.walk.getVert 5) ≤ F := by
    apply le_inf (Escape.EdgeTransfer.edge_Z_le _ _ hc hct)
    have he := Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
      (PathCentrality.LocalCommutator.moduleFacts common) _ _ hc hct
    rw [he]
    exact inf_le_right.trans (centralizer_le hAT)
  have hi : F.relIndex U = 2 := by
    have hn : F.relIndex U ≠ 0 := index_ne_zero_of_finite
    have hb := relIndex_le_of_le_left hZF
      (show (Z R (p.walk.getVert 5)).relIndex U ≠ 0 from index_ne_zero_of_finite)
    have he : (Z R (p.walk.getVert 5)).relIndex U = 2 := earlier.edge_Z_index _ _ hc hct
    omega
  have hcomm := moving_orbit_commutator_le_line common earlier p
  rw [commutator_comm] at hcomm
  have hCA : ⁅U,A⁆ ≤ centralizer (A : Set (FreeAmalgam R)) := by
    intro x hx y hy
    obtain ⟨z,hz,rfl⟩ := H_le_localCenter_of_central R (alpha R)
      (earlier.centrality _ rfl) (hcomm hx).1
    exact congrArg Subtype.val ((mem_center_iff.mp hz)
      ⟨y,(orbitMovingGroup_le_Q earlier q hy).1⟩)
  rw [DistanceFour.Early.actor_index_eq_displacement_card_of_fixed_index_two U A
    (hAG.trans (Z_normalized R _)) hCA hi]
  have hcard : Nat.card (H R (alpha R) ⊓ H R (p.walk.getVert 8) : Subgroup (FreeAmalgam R)) = 2 := by
    have f := (Early.firstFactsOnPath source common earlier p).forward 4
      (by decide) (by decide) (by decide)
    have he := f.commutator_card
    rw [f.commutator_eq] at he
    simpa only [p.center_eq, Nat.reduceAdd] using he
  let : Finite (H R (alpha R) ⊓ H R (p.walk.getVert 8) : Subgroup (FreeAmalgam R)) := Nat.finite_of_card_ne_zero (by omega)
  exact (card_le_of_le hcomm).trans hcard.le

/-- The neighboring intersection is fixed modulo the original denominator
by the source actor at d. Only literal earlier products are used. -/
theorem moving_orbit_neighbor_commutator_le (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅orbitMovingGroup (Early.Orbit.SourceApplications.higherPath geometry p) ⊓ Q R (p.walk.getVert 6),
      hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12)⁆ ≤
        hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  let N := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let B := hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12)
  have hct : Adjacent R (p.walk.getVert 6) (p.walk.getVert 7) := p.adjacent (i := 6) (by decide)
  have ht : color R (p.walk.getVert 7) = true := by
    have hn := adjacent_color_ne R hct
    rw [p.even_color (i := 6) (by decide) (by decide)] at hn
    cases h : color R (p.walk.getVert 7) <;> simp_all
  have hprod : (N : Set (FreeAmalgam R)) * (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
      (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)) := by
    simpa only [p.center_eq,Nat.reduceAdd] using
      ((Early.firstFactsOnPath source common earlier p).forward 4
        (by decide) (by decide) (by decide)).hatW_product
  obtain ⟨hactor,hbound⟩ := SecondLayer.SourceRecognition.first_actor_source common earlier p
  have hB : B ≤ Mbar R := by
    intro b hb
    have hbT : b ∈ Q R (p.walk.getVert 5) := by
      rw [← SetLike.mem_coe, ← hactor]
      exact ⟨b,hb,1,(Q R (alpha R)).one_mem,mul_one b⟩
    have ha : Adjacent R (alpha R) (p.walk.getVert 5) := by
      simpa only [p.center_eq] using p.adjacent (i := 4) (by decide)
    simpa only [alpha,stabilizer_m_base] using hbT.2 _ (adjacent_symm R ha)
  have hZdN : Z R (p.walk.getVert 8) ≤ N :=
    (PathCentrality.Z_le_localZSpan R _ _).trans
      (Escape.Initial.Natural.conjugatesIn_contains _ _)
  have hBN : B ≤ normalizer N := hB.trans (by
    dsimp only [N]
    simpa only [alpha,stabilizer_m_base] using hatW_normalized R (alpha R)
      (p.walk.getVert 6) (p.walk.getVert 8))
  apply commutator_le.mpr
  intro x hx b hb
  have hxT := Q_le_adjacent_h R ht hct hx.2
  change x ∈ (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)) at hxT
  rw [← hprod] at hxT
  obtain ⟨w,hw,z,hz,rfl⟩ := hxT
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hc : ⁅z,b⁆ ∈ N := by
    rw [commutator_comm] at hbound
    exact hZdN (hbound (commutator_mem_commutator hz hb))
  exact N.mul_mem (N.mul_mem (N.mul_mem hw hc) (N.inv_mem hw))
    ((le_normalizer_iff_commutator_le_left.mp hBN) (commutator_mem_commutator hw hb))

/-- The whole original actor at d fixes a subgroup of index at most two
in the actual moving orbit quotient. -/
theorem MovingModule.source_fixed_index (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MovingModule source (Early.Orbit.SourceApplications.higherPath geometry p)) :
    let := s.normal
    (FixedPoints.subgroup
      ((SecondLayer.Recognition.Displacement.actorImage source
        (hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12))).map s.action)
      (MovingSpace (Early.Orbit.SourceApplications.higherPath geometry p))).index ≤ 2 := by
  let := s.normal
  let := s.finite
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  let A := orbitMovingGroup q
  let N := hatW R (alpha R) (q.walk.getVert 6) (q.walk.getVert 8)
  let B := hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12)
  let : (N.subgroupOf A).Normal := s.normal
  let π := QuotientGroup.mk' (N.subgroupOf A)
  let F := FixedPoints.subgroup ((SecondLayer.Recognition.Displacement.actorImage source B).map s.action)
    (MovingSpace q)
  have hc := moving_orbit_neighbor_commutator_le common earlier p
  have hK : (Q R (p.walk.getVert 6)).subgroupOf A ≤ F.comap π := by
    intro x hx a
    obtain ⟨g,⟨m,hm,rfl⟩,ha⟩ := a.property
    let y : A := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp (orbitMovingGroup_normalized q) _ ⟨m,rfl⟩ _ x.property⟩
    change (a : MulAut (MovingSpace q)) (π x) = π x
    rw [← ha]
    change s.action (source.projection m) (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [s.conjugation m x y rfl]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ / (x : FreeAmalgam R) ∈ N
    rw [commutator_comm] at hc
    have hxK : (x : FreeAmalgam R) ∈ orbitMovingGroup q ⊓ Q R (p.walk.getVert 6) := ⟨x.property,hx⟩
    have hbB : embedM R m ∈ B := hm
    have hz := hc (commutator_mem_commutator hbB hxK)
    simpa only [N,q,Early.Orbit.SourceApplications.higherPath,commutatorElement_def,div_eq_mul_inv] using hz
  have hi := index_dvd_of_le hK
  rw [F.index_comap_of_surjective (QuotientGroup.mk'_surjective _)] at hi
  have hb := moving_orbit_neighbor_index_le_two common earlier p
  have hn : (Q R (p.walk.getVert 6)).relIndex A ≠ 0 := by
    let := finite_stabilizer R (alpha R)
    let : Finite A := Finite.of_injective
      (inclusion ((orbitMovingGroup_le_Q earlier q).trans (fun _ hx => hx.1))) (inclusion_injective _)
    exact index_ne_zero_of_finite
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hi).trans hb

/-- The precise small-involution hypothesis, proved for the actual source action. -/
theorem MovingModule.source_small_involution (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MovingModule source (Early.Orbit.SourceApplications.higherPath geometry p)) :
    let := s.normal; Escape.Initial.Natural.Splitting.HasSmallInvolution s.action := by
  let := s.normal
  let := s.finite
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  let : IsElementaryAbelian 2 (MovingSpace q) := s.elementary earlier q
    (OrbitGeometry.Source.Q_commutator_le common earlier p)
  let B := hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12)
  let P := SecondLayer.Recognition.Displacement.actorImage source B
  have hadj : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using p.adjacent (i := 4) (by decide)
  have hcard : Nat.card P = 4 :=
    (SecondLayer.Recognition.Displacement.edge_product_natural_card source common earlier hadj
      (SecondLayer.SourceRecognition.first_actor_source common earlier p).1).2
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 (by rw [hcard]; decide)
  have hne : (t : SL) ≠ 1 := by
    intro he
    have he' : t = 1 := Subtype.ext he
    simp only [he',orderOf_one] at ht
    omega
  have hp : (t : SL)^2 = 1 := by
    have he := pow_orderOf_eq_one t
    rw [ht] at he
    exact congrArg Subtype.val he
  refine ⟨t,hne,hp,?_⟩
  apply MulAut.commutatorAction_card_le_two_of_fixed_index_dvd_two
  have hsub : zpowers (s.action (t : SL)) ≤ P.map s.action :=
    zpowers_le.mpr (mem_map_of_mem _ t.property)
  have hfixed : FixedPoints.subgroup (P.map s.action) (MovingSpace q) ≤
      FixedPoints.subgroup (zpowers (s.action (t : SL))) (MovingSpace q) := by
    intro x hx a
    exact hx ⟨a,hsub a.property⟩
  have hi := index_dvd_of_le hfixed
  have hsmall := s.source_fixed_index common earlier p
  have hn : (FixedPoints.subgroup (P.map s.action) (MovingSpace q)).index ≠ 0 := index_ne_zero_of_finite
  have hn' : (FixedPoints.subgroup (zpowers (s.action (t : SL))) (MovingSpace q)).index ≠ 0 := index_ne_zero_of_finite
  have hb := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hi).trans hsmall
  have hh : (FixedPoints.subgroup (zpowers (s.action (t : SL))) (MovingSpace q)).index = 1 ∨
      (FixedPoints.subgroup (zpowers (s.action (t : SL))) (MovingSpace q)).index = 2 := by omega
  exact (Nat.dvd_prime Nat.prime_two).mpr hh

/-- The source c(X)=1 conclusion on the literal orbit quotient. Its marking
is still the recognition marking; the natural source orientation is subsequent. -/
theorem source_moving_splitting (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ∃ s : MovingModule source (Early.Orbit.SourceApplications.higherPath geometry p),
      let := s.normal
      Nonempty (Escape.Initial.Natural.Splitting.NaturalActionSplitting s.action) := by
  obtain ⟨s,he,hfaith⟩ := source_moving_module common earlier p
  let := s.normal
  let := s.finite
  let := he
  exact ⟨s,Escape.Initial.Natural.Splitting.naturalActionSplitting_of_small_involution
    s.action hfaith (s.source_small_involution common earlier p)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
