module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.ThirdAction

/-!
# A fixed subgroup of index at most four in the complete third quotient

The original edge index gives [hatSix:hatSix intersect Q_c] at most four.
The setwise product hatW_alpha Q_d = Q_t and the preceding commutator bound
[Q_d,hatW_d] <= Z_d show that this intersection is fixed modulo hatW_alpha
by the actual forward actor. Its image under the original projection
therefore fixes a subgroup of the complete third quotient of index at most
four. This uses neither a moving-module model nor a splitting.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)(iv), (4.5.3)(iii),
and the proof of (4.5.4)(iv), printed pp.896--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The source edge bounds the complete third group modulo Q_c by four. -/
theorem third_neighbor_index_le_four (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R)) :
    (Q R (p.walk.getVert 6)).relIndex
      (thirdGroup (Early.Orbit.SourceApplications.higherPath geometry p)) ≤ 4 := by
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  have hct : Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) :=
    adjacent_symm R (p.adjacent (i := 5) (by decide))
  have hat : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using p.adjacent (i := 4) (by decide)
  have ht : color R (p.walk.getVert 5) = true := by
    have hn := adjacent_color_ne R hat
    change false ≠ _ at hn
    cases h : color R (p.walk.getVert 5) <;> simp_all
  have hAT : thirdGroup q ≤ Q R (p.walk.getVert 5) :=
    (q.hatSix_le_Q earlier).trans (Q_le_adjacent_h R ht hat)
  let := finite_stabilizer R (p.walk.getVert 5)
  let : Finite (Q R (p.walk.getVert 5)) := Finite.of_injective
    (inclusion (show Q R (p.walk.getVert 5) ≤ stabilizer R (p.walk.getVert 5) from fun _ hx => hx.1))
    (inclusion_injective _)
  have he := earlier.edge_Q_index _ _ (p.even_color (i := 6) (by decide) (by decide)) hct
  exact (relIndex_le_of_le_right hAT (by exact index_ne_zero_of_finite)).trans_eq he

/-- The neighboring intersection is fixed modulo the original denominator
by the source actor at d. Only literal earlier products are used. -/
theorem third_neighbor_commutator_le (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅thirdGroup (Early.Orbit.SourceApplications.higherPath geometry p) ⊓ Q R (p.walk.getVert 6),
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
theorem ThirdModule.source_fixed_index (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : ThirdModule source (Early.Orbit.SourceApplications.higherPath geometry p)) :
    let := s.normal
    (FixedPoints.subgroup
      ((SecondLayer.Recognition.Displacement.actorImage source
        (hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12))).map s.action)
      (ThirdSpace (Early.Orbit.SourceApplications.higherPath geometry p))).index ≤ 4 := by
  let := s.normal
  let := s.finite
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  let A := thirdGroup q
  let N := hatW R (alpha R) (q.walk.getVert 6) (q.walk.getVert 8)
  let B := hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12)
  let : (N.subgroupOf A).Normal := s.normal
  let π := QuotientGroup.mk' (N.subgroupOf A)
  let F := FixedPoints.subgroup ((SecondLayer.Recognition.Displacement.actorImage source B).map s.action)
    (ThirdSpace q)
  have hc := third_neighbor_commutator_le common earlier p
  have hK : (Q R (p.walk.getVert 6)).subgroupOf A ≤ F.comap π := by
    intro x hx a
    obtain ⟨g,⟨m,hm,rfl⟩,ha⟩ := a.property
    let y : A := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp (thirdGroup_normalized q) _ ⟨m,rfl⟩ _ x.property⟩
    change (a : MulAut (ThirdSpace q)) (π x) = π x
    rw [← ha]
    change s.action (source.projection m) (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [s.conjugation m x y rfl]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ / (x : FreeAmalgam R) ∈ N
    rw [commutator_comm] at hc
    have hxK : (x : FreeAmalgam R) ∈ thirdGroup q ⊓ Q R (p.walk.getVert 6) := ⟨x.property,hx⟩
    have hbB : embedM R m ∈ B := hm
    have hz := hc (commutator_mem_commutator hbB hxK)
    simpa only [N,q,Early.Orbit.SourceApplications.higherPath,commutatorElement_def,div_eq_mul_inv] using hz
  have hi := index_dvd_of_le hK
  rw [F.index_comap_of_surjective (QuotientGroup.mk'_surjective _)] at hi
  have hb := third_neighbor_index_le_four earlier p
  have hn : (Q R (p.walk.getVert 6)).relIndex A ≠ 0 := by
    let := finite_stabilizer R (alpha R)
    let : Finite A := Finite.of_injective
      (inclusion ((q.hatSix_le_Q earlier).trans (fun _ hx => hx.1))) (inclusion_injective _)
    exact index_ne_zero_of_finite
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hi).trans hb


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
