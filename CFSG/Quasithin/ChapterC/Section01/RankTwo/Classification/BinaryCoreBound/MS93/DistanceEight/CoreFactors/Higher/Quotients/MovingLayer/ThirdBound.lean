module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.ThirdFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.MovingBound

/-!
# The source upper bound for the complete moving layer

An actual involution is chosen in the forward edge actor of order four.
Its fixed index on hatSix/hatW is at most four. The three-conjugate bound
then gives moving order at most sixty-four. The source residual surjects
onto SL3(2), so the intrinsic moving subgroup is exactly the image of
[hatSix,Ltilde] under the original quotient map. Its order is the stated
relative index. No orbit-generation, independence or module-model premise
is imposed on the source consumer.

Together with the actual commutator row of order sixty-four, this discharges
the size premise in the natural-pair recognition of MS93 (4.5.4)(iv).
The row and its exact action are supplied by Center.CommutatorRows.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (4.5.4)(iv), p.899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- An actual involution in the forward edge actor fixes index at most four. -/
theorem ThirdModule.source_involution_fixed_four (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : ThirdModule source (Early.Orbit.SourceApplications.higherPath geometry p)) :
    let := s.normal; ∃ t : SL, t ≠ 1 ∧ t ^ 2 = 1 ∧
      (FixedPoints.subgroup (zpowers (s.action t))
        (ThirdSpace (Early.Orbit.SourceApplications.higherPath geometry p))).index ≤ 4 := by
  let := s.normal
  let := s.finite
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  let : IsElementaryAbelian 2 (ThirdSpace q) := s.elementary earlier q
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
  have hsub : zpowers (s.action (t : SL)) ≤ P.map s.action :=
    zpowers_le.mpr (mem_map_of_mem _ t.property)
  have hfixed : FixedPoints.subgroup (P.map s.action) (ThirdSpace q) ≤
      FixedPoints.subgroup (zpowers (s.action (t : SL))) (ThirdSpace q) := by
    intro x hx a
    exact hx ⟨a,hsub a.property⟩
  have hi := index_dvd_of_le hfixed
  have hsmall := s.source_fixed_index common earlier p
  have hn : (FixedPoints.subgroup (P.map s.action) (ThirdSpace q)).index ≠ 0 := index_ne_zero_of_finite
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hi).trans hsmall

/-- The ambient residual commutator maps onto the intrinsic moving summand. -/
theorem ThirdModule.residual_image (p : Higher.SourcePath (alpha R))
    (s : ThirdModule source p) : let := s.normal
    (⁅thirdGroup p,Ltilde R (alpha R)⁆.subgroupOf (thirdGroup p)).map
      (QuotientGroup.mk' ((hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf
        (thirdGroup p))) = commutatorAction s.action.range (ThirdSpace p) := by
  let := s.normal
  let P := stabilizer R (alpha R)
  let e := FirstDirect.baseEquiv R
  let ζ : P →* SL := source.projection.comp e.symm.toMonoidHom
  let τ : P →* MulAut (ThirdSpace p) := s.action.comp ζ
  have hPX : P ≤ normalizer (thirdGroup p) := by
    simpa only [P,alpha,stabilizer_m_base] using thirdGroup_normalized p
  have hconj (g : P) (x : thirdGroup p) :
      τ g (QuotientGroup.mk x) = QuotientGroup.mk
        (⟨(g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
          (mem_normalizer_iff.mp (hPX g.property) x).mp x.property⟩ : thirdGroup p) := by
    obtain ⟨m,rfl⟩ := e.surjective g
    change s.action (source.projection (e.symm (e m))) _ = _
    rw [e.symm_apply_apply]
    exact s.conjugation m x _ rfl
  have hLm : L.map source.projection = ⊤ := by
    have hm := congrArg (Subgroup.map source.projection) source.residual_sup_core
    rw [Subgroup.map_sup, ← source.projection_kernel, map_ker_self, sup_bot_eq,
      map_top_of_surjective _ source.projection_surjective] at hm
    exact hm
  have hJ : ((Ltilde R (alpha R)).subgroupOf P).map τ = s.action.range := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨ζ x,rfl⟩
    · rintro _ ⟨g,rfl⟩
      obtain ⟨m,hm,hg⟩ := hLm.ge (mem_top g)
      refine ⟨e m,?_,?_⟩
      · change embedM R m ∈ Ltilde R (alpha R)
        rw [Ltilde_alpha,source.residual]
        exact mem_map_of_mem _ hm
      · change s.action (source.projection (e.symm (e m))) = s.action g
        rw [e.symm_apply_apply,hg]
  have hi := quotient_conjugation_commutatorAction_eq_image P (thirdGroup p)
    (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) (Ltilde R (alpha R))
    hPX (Ltilde_le_stabilizer _) s.normal τ hconj
  rw [hJ] at hi
  exact hi.symm

/-- The full literal third moving quotient has order at most sixty-four. -/
theorem third_residual_relIndex_le_sixtyFour (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).relIndex
      ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        Ltilde R (alpha R)⁆ ≤ 64 := by
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  have hQ := OrbitGeometry.Source.Q_commutator_le common earlier p
  obtain ⟨s⟩ := thirdModule source earlier q hQ
  let := s.normal
  let := s.finite
  let : IsElementaryAbelian 2 (ThirdSpace q) := s.elementary earlier q hQ
  obtain ⟨t,hne,ht,hfix⟩ := s.source_involution_fixed_four common earlier p
  have hb := moving_card_le_sixtyFour s.action t ht hne hfix
  rw [← s.residual_image q] at hb
  have hcomm : ⁅thirdGroup q,Ltilde R (alpha R)⁆ ≤ thirdGroup q :=
    le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer _).trans (by
      simpa only [alpha,stabilizer_m_base] using thirdGroup_normalized q))
  rw [← relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hcomm] at hb
  exact hb

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
