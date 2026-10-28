module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.CoreQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.ThirdFixed

/-!
# Involution displacement on the literal core quotient

The forward second-hat actor has an order-four image under the original
source projection. It therefore contains a source lift of a nonidentity
involution. More precisely, the natural subgroup at the critical endpoint
p12 already escapes the original two-core: its fixed complement lies in
Z(p10), hence in that two-core. Thus the lift may be chosen as an actual
involution in that natural subgroup. The neighboring displacement lies in
both the original and forward second hats.

The neighboring core intersection has index at most four in K.
On the elementary quotient K/Vcirc, displacement is a homomorphism; counting
its restriction bounds the full fixed index by four times the complete
neighboring displacement modulo Vcirc.

The existing third-layer calculation puts that displacement inside the
second hat. It does not bound its image modulo Vcirc. The remaining bound
by four is explicit here. In particular, the exact index factorization
retains the first-hat intersection, including any residual fixed kernel.
No fixed-factor equality or center-size bound is assumed or asserted.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)(iv), (4.5.3)--(4.5.5),
printed pp.896--899. The counting step is the same restriction argument
used for the first-hat displacement in (4.5.3)(i).
-/

public section
noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center.CoreQuotient
open Higher

private def differenceHom {E : Type*} [Group E] [IsMulCommutative E]
    (a : MulAut E) : E →* E where
  toFun x := a x / x
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, div_eq_mul_inv, mul_inv_rev]; ac_rfl

private theorem card_range_le_index_mul_card_map {A E : Type*} [Group A] [Group E]
    [Finite A] (f : A →* E) (F : Subgroup A) :
    Nat.card f.range ≤ F.index * Nat.card (F.map f) := by
  let N := F.map f
  have hle : N ≤ f.range := map_le_range f F
  have hc := relIndex_mul_relIndex (⊥ : Subgroup E) N f.range bot_le hle
  rw [relIndex_bot_left, relIndex_bot_left] at hc
  have hi : N.relIndex f.range ≤ F.index := by
    rw [← index_comap]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero F.index_ne_zero_of_finite)
      (index_dvd_of_le (le_comap_map f F))
  rw [← hc, mul_comm]
  exact Nat.mul_le_mul_right _ hi

variable {M : Type*} [Group M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The actual forward actor, whose image under the source projection has order four. -/
abbrev forwardActor (p : Early.SourcePath R (alpha R)) : Subgroup (FreeAmalgam R) :=
  hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12)

/-- Displacement of the neighboring core intersection by a single literal actor.
The denominator is deliberately not enlarged to the first or second hat layer. -/
abbrev neighborDisplacement (p : Early.SourcePath R (alpha R)) (m : M) :
    Subgroup (FreeAmalgam R) :=
  ⁅core R (alpha R) ⊓ Q R (p.walk.getVert 6), zpowers (embedM R m)⁆

theorem neighborDisplacement_le_core (p : Early.SourcePath R (alpha R)) (m : M) :
    neighborDisplacement p m ≤ core R (alpha R) := by
  apply (commutator_mono inf_le_left le_rfl).trans
  apply le_normalizer_iff_commutator_le_left.mp
  apply zpowers_le.mpr
  apply DistanceTwo.core_normalized _
  simpa only [alpha, stabilizer_m_base] using
    (show embedM R m ∈ Mbar R from ⟨m, rfl⟩)

variable [Finite M]

/-- The earlier edge index gives the first factor of four in the displacement budget. -/
theorem core_neighbor_index_le_four (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (Q R (p.walk.getVert 6)).relIndex (core R (alpha R)) ≤ 4 := by
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  let := finite_stabilizer R (alpha R)
  let : Finite (Quotients.MovingLayer.thirdGroup q) := Finite.of_injective
    (inclusion ((q.hatSix_le_Q earlier).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  exact (relIndex_le_of_le_right
    (Early.Orbit.Source.Complete.core_le_third_hat common earlier p)
    (show (Q R (p.walk.getVert 6)).relIndex (Quotients.MovingLayer.thirdGroup q) ≠ 0 from
      index_ne_zero_of_finite)).trans
    (Quotients.MovingLayer.third_neighbor_index_le_four earlier p)

/-- The existing geometric estimate puts the error inside the second hat.
It does not bound that error modulo Vcirc. -/
theorem neighborDisplacement_le_second (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (m : M) (hm : embedM R m ∈ forwardActor p) :
    neighborDisplacement p m ≤
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) :=
  (commutator_mono
    (inf_le_inf (Early.Orbit.Source.Complete.core_le_third_hat common earlier p) le_rfl)
    (zpowers_le.mpr hm)).trans
      (Quotients.MovingLayer.third_neighbor_commutator_le common earlier p)

/-- The neighboring core intersection fixes the center of the forward second
hat. Its commutator with a forward actor therefore lies in that hat as well
as in the original second hat. This does not discard the first-hat kernel. -/
theorem neighborDisplacement_le_forwardActor (geometry : Geometry R) (p : Early.SourcePath R (alpha R))
    (m : M) (hm : embedM R m ∈ forwardActor p) :
    neighborDisplacement p m ≤ forwardActor p := by
  have hcd : (cosetGraph R).dist (p.walk.getVert 6) (p.walk.getVert 8) = 2 :=
    p.distance (geometry := geometry) (by decide) (by decide)
  have hnorm : core R (alpha R) ⊓ Q R (p.walk.getVert 6) ≤
      normalizer (forwardActor p) :=
    inf_le_right.trans ((Q_le_stabilizer_of_dist_two R _ _
      (p.even_color (by decide) (by decide)) hcd).trans (hatW_normalized R _ _ _))
  rw [neighborDisplacement, commutator_comm]
  exact (commutator_mono (zpowers_le.mpr hm) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hnorm)


/-- The distant natural subgroup supplies an actual involution in M, not
only a lift whose source image is involutory. The same actor has its literal
neighboring displacement in both second hats. The index of this displacement
modulo Vcirc is not asserted here. -/
theorem exists_endpoint_involution (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R)) :
    ∃ m : M, embedM R m ∈ U R (p.walk.getVert 12) ∧
      embedM R m ∈ forwardActor p ∧ m ^ 2 = 1 ∧
      source.projection m ^ 2 = 1 ∧ source.projection m ≠ 1 ∧
      neighborDisplacement p m ≤
        hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ⊓ forwardActor p := by
  let f := p.walk.getVert 12
  let e := p.walk.getVert 10
  let t := p.walk.getVert 11
  have hf : color R f = false := p.even_color (by decide) (by decide)
  have he : color R e = false := p.even_color (by decide) (by decide)
  have hft : Adjacent R f t := adjacent_symm R (p.adjacent (i := 11) (by decide))
  have het : Adjacent R e t := p.adjacent (i := 10) (by decide)
  have hZa : ¬ Z R f ≤ Q R (alpha R) := by
    have hp := p.critical_pair earlier (i := 4) (by decide) (by decide)
    have hh := common.critical_reverse _ (p.even_color (i := 4) (by decide) (by decide))
      _ hf hp
    simpa only [p.center_eq, Nat.reduceAdd] using hh.2
  have hfixed : Z R f ⊓ centralizer (stabilizer R f : Set (FreeAmalgam R)) ≤ Z R e := by
    apply le_trans _ (Escape.EdgeTransfer.edge_Z_le e t he het)
    rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
      (PathCentrality.LocalCommutator.moduleFacts common) f t hf hft]
    exact inf_le_inf_left _ (centralizer_le (fun _ hx => hx.2 f (adjacent_symm R hft)))
  have heQ : Z R e ≤ Q R (alpha R) := by
    apply Z_le_Q_of_dist_lt R e (geometry.exists_critical e he)
    rw [geometry.distance_constant e he]
    change (cosetGraph R).dist e (alpha R) < geometry.b R
    rw [earlier.distance, ← p.center_eq, SimpleGraph.dist_comm]
    rw [p.distance (geometry := geometry) (i := 4) (j := 10) (by decide) (by decide)]
    decide
  have hu : ¬ U R f ≤ Q R (alpha R) := by
    intro h
    apply hZa
    rw [(PathCentrality.LocalCommutator.naturalStructure common).decomposition_at f hf]
    exact sup_le h (hfixed.trans heQ)
  obtain ⟨u,hu,huQ⟩ := SetLike.not_le_iff_exists.mp hu
  have huf : u ∈ Z R f := U_le_Z R f hu
  have hfa : (cosetGraph R).dist f (alpha R) = 8 := by
    rw [← p.center_eq, SimpleGraph.dist_comm]
    exact p.distance (geometry := geometry) (i := 4) (j := 12) (by decide) (by decide)
  have hlocal : u ∈ Mbar R := by
    have h := geometry.Z_le_stabilizer_of_dist_le_b f hf (alpha R)
      (by rw [hfa, earlier.distance]) huf
    simpa only [alpha, stabilizer_m_base] using h
  obtain ⟨m,rfl⟩ := hlocal
  have hmB : embedM R m ∈ forwardActor p :=
    (Escape.Initial.Natural.conjugatesIn_contains _ _)
      (PathCentrality.Z_le_localZSpan R f e huf)
  have hm2 : m ^ 2 = 1 := by
    apply embedM_injective R
    rw [map_pow, map_one]
    let := geometry.Z_elementary (by rw [earlier.distance]; decide) f hf
    exact elemPow_eq_one_of_isElementaryAbelian _ huf
  have hne : source.projection m ≠ 1 := by
    intro hm
    apply huQ
    rw [Q_alpha R source.two_group source.core_le]
    exact mem_map_of_mem _ (source.projection_kernel ▸ MonoidHom.mem_ker.mpr hm)
  exact ⟨m,hu,hmB,hm2,by rw [← map_pow,hm2,map_one],hne,
    le_inf (neighborDisplacement_le_second common earlier p m hmB)
      (neighborDisplacement_le_forwardActor geometry p m hmB)⟩

/-- Choose the forward involution from the actual natural subgroup at p12. -/
theorem exists_forward_involution (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ∃ m : M, embedM R m ∈ forwardActor p ∧
      source.projection m ^ 2 = 1 ∧ source.projection m ≠ 1 := by
  obtain ⟨m,_,hm,_,ht,hne,_⟩ := exists_endpoint_involution common earlier p
  exact ⟨m,hm,ht,hne⟩

/-- The exact quotient fixed index, retaining all neighboring displacement,
including its intersection with the first hat and the residual fixed kernel. -/
theorem fixed_index_le_four_mul_neighbor_displacement
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    [IsElementaryAbelian 2 (Space R)] (p : Early.SourcePath R (alpha R)) (m : M) :
    (FixedPoints.subgroup (zpowers (localAction R m)) (Space R)).index ≤
      4 * (Vcirc R (alpha R)).relIndex (neighborDisplacement p m) := by
  let K := core R (alpha R)
  let D := Vcirc R (alpha R)
  let E := neighborDisplacement p m
  let F := (Q R (p.walk.getVert 6)).subgroupOf K
  let π := QuotientGroup.mk' (D.subgroupOf K)
  let f := (differenceHom (localAction R m)).comp π
  let := DistanceTwo.finite_core (R := R) (alpha R)
  have hEK : E ≤ K := neighborDisplacement_le_core p m
  have hmap : F.map f ≤ (E.subgroupOf K).map π := by
    rintro _ ⟨x, hx, rfl⟩
    let y : K := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp (HomSaturation.core_normalized (R := R)) _ ⟨m, rfl⟩ _ x.property⟩
    have he : ((y / x : K) : FreeAmalgam R) ∈ E := by
      dsimp only [E, neighborDisplacement]
      rw [commutator_comm]
      have h := commutator_mem_commutator (mem_zpowers (embedM R m))
        (show (x : FreeAmalgam R) ∈ core R (alpha R) ⊓ Q R (p.walk.getVert 6) from
          ⟨x.property, hx⟩)
      simpa only [y, Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
        commutatorElement_def, div_eq_mul_inv] using h
    refine ⟨y / x, he, ?_⟩
    change π (y / x) = localAction R m (π x) / π x
    rw [map_div]
    exact congrArg (fun z => z / π x) (localAction_conjugation R m x y rfl).symm
  have hcard : Nat.card ((E.subgroupOf K).map π) = D.relIndex E := by
    rw [← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hEK]
  have hkernel : (differenceHom (localAction R m)).ker =
      FixedPoints.subgroup (zpowers (localAction R m)) (Space R) := by
    ext x
    rw [MonoidHom.mem_ker, MulAut.mem_fixed_zpowers_iff]
    change localAction R m x / x = 1 ↔ localAction R m x = x
    exact div_eq_one
  have hrange : f.range = (differenceHom (localAction R m)).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      ← MonoidHom.range_eq_map]
  have hbound := card_range_le_index_mul_card_map f F
  rw [hrange, ← index_ker, hkernel] at hbound
  apply hbound.trans
  apply Nat.mul_le_mul (core_neighbor_index_le_four common earlier p)
  exact (card_le_of_le hmap).trans hcard.le

/-- The remaining small-error estimate on a chosen source actor yields the
requested involution displacement bound on the literal core quotient. -/
theorem exists_involution_of_neighbor_displacement
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    [IsElementaryAbelian 2 (Space R)] (p : Early.SourcePath R (alpha R))
    (hsmall : ∀ m : M, embedM R m ∈ forwardActor p →
      source.projection m ^ 2 = 1 → source.projection m ≠ 1 →
      (Vcirc R (alpha R)).relIndex (neighborDisplacement p m) ≤ 4) :
    ∃ m : M, source.projection m ^ 2 = 1 ∧ source.projection m ≠ 1 ∧
      (FixedPoints.subgroup (zpowers (localAction R m)) (Space R)).index ≤ 16 := by
  obtain ⟨m, hm, ht, hne⟩ := exists_forward_involution common earlier p
  exact ⟨m, ht, hne, (fixed_index_le_four_mul_neighbor_displacement common earlier p m).trans
    (Nat.mul_le_mul_left 4 (hsmall m hm ht hne))⟩

/-- A single favorable actor suffices; no bound on every forward involution
is needed in the final source assembly. -/
theorem fixed_index_le_sixteen_of_neighbor_displacement
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    [IsElementaryAbelian 2 (Space R)] (p : Early.SourcePath R (alpha R)) (m : M)
    (hsmall : (Vcirc R (alpha R)).relIndex (neighborDisplacement p m) ≤ 4) :
    (FixedPoints.subgroup (zpowers (localAction R m)) (Space R)).index ≤ 16 :=
  (fixed_index_le_four_mul_neighbor_displacement common earlier p m).trans
    (Nat.mul_le_mul_left 4 hsmall)

/-- Separating the nonfixed first-hat quotient from its kernel retains the
factor which a bound on the higher quotients alone cannot remove. -/
theorem neighbor_displacement_index_factors
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R)) (m : M) :
    (Vcirc R (alpha R)).relIndex
        (hatV R (alpha R) (p.walk.getVert 6) ⊓ neighborDisplacement p m) *
      (hatV R (alpha R) (p.walk.getVert 6)).relIndex (neighborDisplacement p m) =
      (Vcirc R (alpha R)).relIndex (neighborDisplacement p m) := by
  have hle : Vcirc R (alpha R) ≤ hatV R (alpha R) (p.walk.getVert 6) := by
    rw [(Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
    exact le_sup_left
  simpa only [inf_eq_left.mpr hle] using relIndex_inf_mul_relIndex
    (Vcirc R (alpha R)) (hatV R (alpha R) (p.walk.getVert 6)) (neighborDisplacement p m)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center.CoreQuotient
