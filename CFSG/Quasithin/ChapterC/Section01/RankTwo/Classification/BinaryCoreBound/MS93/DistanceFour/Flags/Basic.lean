module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Source
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.Elementary
public import Mathlib.GroupTheory.Abelianization.Defs
public import Theory.GroupTheory.Commutator.ConjugateGeneration
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Geometric and commutator deductions for the MS93 distance-four flags

The actual noncentral distance-two generators span the radius subgroup together
with its center B. Local transitivity puts Z in every starred span. The
three-subgroups lemma and the fixed-point-free moving layer show that the
starred intersection centralizes Q. Involution generation puts its squares in
V′ = U; the definition of B makes those squares fixed, so they vanish.

Residual commutator idempotence is applied in the finite vertex stabilizer,
then mapped to the free amalgam. No finiteness of that amalgam is assumed.

The rank-one calculation itself remains explicit in `RankOneConclusions`:
V′ = U, [Q,Ltilde] ≤ V, and the edge-star commutator bound. This module does
not construct those premises from EarlyFacts, and does not identify the center
of the commutator core or assume generation of V by B and that core.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.8)--(4.6.10), printed pp.905--908, and the core/moving equality
used on p.909. The remaining rank-one argument is on pp.905--908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags
variable {M : Type*} [Group M] {R : Subgroup M}

/-- Every radius-two layer lies in the local kernel when the critical distance exceeds two. -/
theorem V_le_Q (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) : V R a ≤ Q R a := by
  have hz : Z R a ≤ Q R a := (geometry.omega_bound a ha
    (by rw [geometry.distance_constant a ha]; exact lt_trans (by decide) hlarge)).trans
      (omegaCenter_le _)
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  by_cases hcol : color R t = false
  · apply Z_le_Q_of_dist_lt R t (geometry.exists_critical t hcol)
    rw [geometry.distance_constant t hcol]
    exact lt_of_le_of_lt ht hlarge
  · have hc : color R t = true := by cases hh : color R t <;> simp_all
    obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist t a
    have hnEven : ¬ Even ((cosetGraph R).dist t a) := by
      rw [← hp, walk_even_iff_color_eq, hc, ha]
      decide
    rw [Nat.even_iff] at hnEven
    have hd : (cosetGraph R).dist t a = 1 := by omega
    have hadj : Adjacent R a t :=
      adjacent_symm R ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hd))
    apply le_trans _ hz
    rw [Z, if_neg hcol]
    rw [Z, if_pos ha]
    exact le_iSup_of_le t (le_iSup_of_le hadj le_rfl)

/-- Residual commutator idempotence, proved inside the finite vertex stabilizer. -/
theorem core_idempotent [Finite M] {L : Subgroup M} (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) : ⁅core R a, Ltilde R a⁆ = core R a := by
  let := finite_stabilizer R a
  let := Q_normal R a
  have hq : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  have hh := commutator_isPPerfect_idempotent (pResidual 2 (stabilizer R a))
    ((Q R a).subgroupOf (stabilizer R a)) (isPPerfect_pResidual 2)
    ((Q_isPGroup R source.two_group source.core_le a ha).comap_subtype)
    le_normalizer_of_normal
  have hmap := congrArg (Subgroup.map (stabilizer R a).subtype) hh
  simpa only [map_commutator, map_subgroupOf_eq_of_le hq, core, Ltilde] using hmap

/-- The core containment from (4.6.9) identifies the moving radius subgroup, as used on p.909. -/
theorem core_eq_moving_of_le_radius [Finite M] {L : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (hcore : core R a ≤ V R a) :
    core R a = Vcirc R a := by
  apply le_antisymm
  · rw [← core_idempotent source a ha]
    exact commutator_mono hcore le_rfl
  · exact commutator_mono (V_le_Q geometry hlarge a ha) le_rfl

private theorem square_mem_derived_of_omegaOne {G : Type*} [Group G]
    (P : Subgroup G) (hP : omegaOneAmbient P = P) {x : G} (hx : x ∈ P) :
    x ^ 2 ∈ ⁅P, P⁆ := by
  let f : P →* Abelianization P := (powMonoidHom 2).comp Abelianization.of
  have hle : P ≤ f.ker.map P.subtype := by
    conv_lhs => rw [← hP]
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro y hy hy2
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    change (Abelianization.of (⟨y, hy⟩ : P)) ^ 2 = 1
    rw [← map_pow, show (⟨y, hy⟩ : P) ^ 2 = 1 from Subtype.ext hy2, map_one]
  obtain ⟨y, hy, he⟩ := hle hx
  change (y : G) = x at he
  have hpow : y ^ 2 ∈ commutator P := by
    rw [← Abelianization.ker_of P]
    change Abelianization.of (y ^ 2) = 1
    rw [map_pow]
    exact hy
  have hh := mem_map_of_mem P.subtype hpow
  simpa only [_root_.commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype, subtype_apply, coe_pow, he] using hh

/-- The common direct-sum decomposition leaves no fixed points in the moving natural layer. -/
theorem U_fixed_eq_bot {L : Subgroup M} {source : LocalSource L R}
    {geometry : Geometry R} (common : CommonFacts R source geometry)
    (a : Vertex R) (ha : color R a = false) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
  have hbase : U R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact (disjoint_iff.mp common.disjoint).le ⟨hx.1, DistanceEight.U_le_Z R _ hx.1, hx.2⟩
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hu := U_act R g (alpha R)
  have hl := Ltilde_act R g (alpha R)
  simp only [alpha, act_mVertex, one_mul] at hu hl
  apply le_bot_iff.mp
  rintro x ⟨hx, hc⟩
  rw [hu] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyc : y ∈ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) := by
    intro l hll
    have hll' : (MulAut.conj g⁻¹) l ∈ Ltilde R (mVertex R g) := by
      rw [hl]
      exact mem_map_of_mem _ hll
    have he := hc _ hll'
    apply (MulAut.conj g⁻¹).injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using he
  have hy1 : y = 1 := hbase.le ⟨hy, hyc⟩
  simp only [hy1, map_one, mem_bot]

/-- Every stabilizer conjugate in the actual starred span stays in the radius-two subgroup. -/
theorem star_le_radius (geometry : Geometry R) (a b : Vertex R) :
    VStar R geometry a b ≤ V R a := by
  apply iSup_le
  intro g
  have hv := DistanceEight.V_normalized R a g.property
  rw [mem_normalizer_iff_map_conj_eq] at hv
  rw [← hv]
  apply map_mono
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact le_iSup_of_le t (le_iSup_of_le (ht.1.1.le) le_rfl)

open scoped commutatorElement in
/-- The quotient-centralizer definition of B gives its literal commutator bound. -/
theorem B_commutator_le_Z (geometry : Geometry R) (a : Vertex R)
    (hV : V R a ≤ stabilizer R a) :
    ⁅B R a (geometry.Z_normal a), Ltilde R a⁆ ≤ Z R a := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl x hx
  exact ((mem_B_iff R a (geometry.Z_normal a) hV x).mp hx).2 l hl

/-- The three-subgroups argument in (4.6.10), with its rank-one inputs explicit. -/
theorem star_intersection_centralizes_Q {L : Subgroup M} {source : LocalSource L R}
    {geometry : Geometry R} (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (a b : Vertex R) (ha : color R a = false)
    (hcore : core R a ≤ V R a)
    (hstar : ⁅VStar R geometry a b, Q R a⁆ ≤ U R a) :
    ⁅VStar R geometry a b ⊓ B R a (geometry.Z_normal a), Q R a⁆ = ⊥ := by
  let K := VStar R geometry a b ⊓ B R a (geometry.Z_normal a)
  have hk : K ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
    intro x hx
    have hb := hx.2
    rw [early.B_eq_center a ha] at hb
    obtain ⟨z, hz, rfl⟩ := hb
    intro v hv
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨v, hv⟩)
  have hfirst : ⁅⁅Q R a, Ltilde R a⁆, K⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hcore.trans (le_centralizer_iff.mp hk)
  have hsecond : ⁅⁅Ltilde R a, K⁆, Q R a⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← geometry.centralizes a ha]
    apply commutator_mono _ le_rfl
    rw [commutator_comm]
    exact (commutator_mono inf_le_right le_rfl).trans
      (B_commutator_le_Z geometry a
        (geometry.V_local a ha (by rw [geometry.distance_constant a ha]; exact common.large_distance)))
  have hthird := commutator_commutator_eq_bot_of_rotate hfirst hsecond
  apply le_bot_iff.mp
  rw [← U_fixed_eq_bot common a ha]
  exact le_inf ((commutator_mono inf_le_left le_rfl).trans hstar)
    (commutator_eq_bot_iff_le_centralizer.mp hthird)

open scoped commutatorElement in
/-- Centralization and square vanishing put the intersection in the actual omega-center. -/
theorem star_intersection_le_Z {L : Subgroup M} {source : LocalSource L R}
    {geometry : Geometry R} (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (a b : Vertex R) (ha : color R a = false)
    (hderived : ⁅V R a, V R a⁆ = U R a) (hcore : core R a ≤ V R a)
    (hstar : ⁅VStar R geometry a b, Q R a⁆ ≤ U R a) :
    VStar R geometry a b ⊓ B R a (geometry.Z_normal a) ≤ Z R a := by
  have hKQ := commutator_eq_bot_iff_le_centralizer.mp
    (star_intersection_centralizes_Q common early a b ha hcore hstar)
  intro x hx
  have hxV := star_le_radius geometry a b hx.1
  have hxQ := V_le_Q geometry common.large_distance a ha hxV
  rw [← common.X_eq_Z a ha]
  apply mem_omegaCenter_iff.mpr
  refine ⟨hxQ, ?_, hKQ hx⟩
  have hx2U : x ^ 2 ∈ U R a := by
    rw [← hderived]
    exact square_mem_derived_of_omegaOne (V R a) (DistanceEight.VBall_omegaOne R a 2) hxV
  have hx2L : x ^ 2 ∈ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    intro l hl
    have hz := ((mem_B_iff R a (geometry.Z_normal a)
      (geometry.V_local a ha (by rw [geometry.distance_constant a ha]; exact common.large_distance)) x).mp hx.2).2 l hl
    have hzX : ⁅l, x⁆ ∈ omegaCenter (Q R a) := by
      rw [← common.X_eq_Z a ha] at hz
      exact hz
    have hz2 := (mem_omegaCenter_iff.mp hzX).2.1
    have hzx : Commute ⁅l, x⁆ x :=
      ((mem_omegaCenter_iff.mp hzX).2.2 x hxQ).symm
    have hc : l * x ^ 2 * l⁻¹ = x ^ 2 := by
      calc
        l * x ^ 2 * l⁻¹ = (l * x * l⁻¹) ^ 2 := by simp only [pow_two]; group
        _ = (⁅l, x⁆ * x) ^ 2 := by rw [← conj_eq_commutatorElement_mul]; rfl
        _ = x ^ 2 := by rw [hzx.mul_pow, hz2, one_mul]
    calc
      l * x ^ 2 = (l * x ^ 2 * l⁻¹) * l := by group
      _ = x ^ 2 * l := by rw [hc]
  exact (U_fixed_eq_bot common a ha).le ⟨hx2U, hx2L⟩

/-- The central layer lies in the preimage of the fixed subgroup of the radius quotient. -/
theorem Z_le_B (geometry : Geometry R) (a : Vertex R)
    (hV : V R a ≤ stabilizer R a) : Z R a ≤ B R a (geometry.Z_normal a) := by
  intro x hx
  apply (mem_B_iff R a (geometry.Z_normal a) hV x).mpr
  refine ⟨Z_le_VBall R a 2 hx, ?_⟩
  intro l hl
  have hcomm : ⁅Ltilde R a, Z R a⁆ ≤ Z R a :=
    le_normalizer_iff_commutator_le_right.mp ((map_subtype_le _).trans (Z_normalized R a))
  exact hcomm (commutator_mem_commutator hl hx)

/-- An adjacent holomorph Z-layer is one of the defining generators at an M-vertex. -/
theorem edge_Z_le (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    Z R b ≤ Z R a := by
  have hb : color R b ≠ false := by simpa only [ha] using (adjacent_color_ne R hab).symm
  rw [Z, if_neg hb]
  conv_rhs => rw [Z, if_pos ha]
  exact le_iSup_of_le b (le_iSup_of_le hab le_rfl)

private theorem map_center_image {G : Type*} [Group G] (P : Subgroup G)
    (e : G ≃* G) :
    ((center P).map P.subtype).map e.toMonoidHom =
      (center (P.map e.toMonoidHom)).map (P.map e.toMonoidHom).subtype := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨e x, mem_map_of_mem _ x.property⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    rintro ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    simpa only [coe_mul, map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg e (congrArg Subtype.val ((mem_center_iff.mp hx) ⟨y, hy⟩))
  · rintro _ ⟨⟨_, x, hx, rfl⟩, hz, rfl⟩
    refine ⟨x, ⟨⟨x, hx⟩, ?_, rfl⟩, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply e.injective
    simpa only [coe_mul, map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg Subtype.val ((mem_center_iff.mp hz) ⟨e y, mem_map_of_mem _ y.property⟩)

/-- The radius-center equality makes B invariant under the original stabilizer action. -/
theorem B_map_conj (geometry : Geometry R) (early : EarlyFacts R geometry)
    (a : Vertex R) (ha : color R a = false) (g : stabilizer R a) :
    (B R a (geometry.Z_normal a)).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom =
      B R a (geometry.Z_normal a) := by
  rw [early.B_eq_center a ha, map_center_image]
  have h := DistanceEight.V_normalized R a g.property
  rw [mem_normalizer_iff_map_conj_eq] at h
  change (V R a).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom = V R a at h
  rw [h]

/-- The noncentral distance-two vertices are invariant under the stabilizer of their center. -/
theorem nu_act (geometry : Geometry R) (early : EarlyFacts R geometry)
    (a t : Vertex R) (ha : color R a = false) (g : stabilizer R a)
    (ht : nu R geometry a t) : nu R geometry a (act R g t) := by
  refine ⟨?_, ?_⟩
  · have hd := dist_act R g t a
    have hga : act R g a = a := g.property
    rwa [hga, ht.1] at hd
  · intro hn
    apply ht.2
    rw [Z_act, ← B_map_conj geometry early a ha g⁻¹] at hn
    exact (map_le_map_iff_of_injective (MulAut.conj (g : FreeAmalgam R)⁻¹).injective).mp hn

/-- A noncentral derived radius subgroup forces a noncentral distance-two generator. -/
theorem exists_nu (geometry : Geometry R) (early : EarlyFacts R geometry)
    (hlarge : 2 < geometry.b R) (a : Vertex R) (ha : color R a = false) :
    ∃ t, nu R geometry a t := by
  by_contra! hn
  have hV := geometry.V_local a ha (by rw [geometry.distance_constant a ha]; exact hlarge)
  have hZB := Z_le_B geometry a hV
  have hVB : V R a ≤ B R a (geometry.Z_normal a) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    by_cases h0 : (cosetGraph R).dist t a = 0
    · have he := (cosetGraph_connected R).dist_eq_zero_iff.mp h0
      simpa only [he] using hZB
    by_cases h1 : (cosetGraph R).dist t a = 1
    · have hadj := adjacent_symm R ((cosetGraph_adj R _ _).mp
        (SimpleGraph.dist_eq_one_iff_adj.mp h1))
      exact (edge_Z_le a t ha hadj).trans hZB
    have h2 : (cosetGraph R).dist t a = 2 := by omega
    by_contra hnb
    exact hn t ⟨h2, hnb⟩
  have hc : V R a ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
    intro x hx
    have hh := hVB hx
    rw [early.B_eq_center a ha] at hh
    obtain ⟨z, hz, rfl⟩ := hh
    intro y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)
  apply early.derived_noncentral a ha
  rw [commutator_eq_bot_iff_le_centralizer.mpr hc]
  exact bot_le

/-- Local transitivity places a noncentral distance-two generator beyond any chosen edge. -/
theorem exists_nu_neighbor [Finite M] (geometry : Geometry R) (early : EarlyFacts R geometry)
    (hlarge : 2 < geometry.b R) (a b : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) :
    ∃ t, nu R geometry a t ∧ Adjacent R b t := by
  obtain ⟨t, ht⟩ := exists_nu geometry early hlarge a ha
  have hed : (cosetGraph R).edist t a = 2 := by
    rw [← ((cosetGraph_connected R) t a).coe_dist_eq_edist, ht.1]
    rfl
  obtain ⟨c, hc⟩ := (SimpleGraph.edist_eq_two_iff.mp hed).2.2
  obtain ⟨htc, hac⟩ := hc
  have htc' := (cosetGraph_adj R _ _).mp htc
  have hac' := (cosetGraph_adj R _ _).mp hac
  obtain ⟨g, hg, hgb⟩ := stabilizer_transitive_neighbors R a hac' hab
  refine ⟨act R g t, nu_act geometry early a t ha ⟨g, hg⟩ ht, ?_⟩
  have hadj := (adjacent_act_iff R g c t).mpr (adjacent_symm R htc')
  rwa [hgb] at hadj

/-- The starred span contains all adjacent omega-centers, hence the full local Z-layer. -/
theorem Z_le_star [Finite M] (geometry : Geometry R) (early : EarlyFacts R geometry)
    (hlarge : 2 < geometry.b R) (a b : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) :
    Z R a ≤ VStar R geometry a b := by
  obtain ⟨t, ht, hbt⟩ := exists_nu_neighbor geometry early hlarge a b ha hab
  have htb : color R t = false := by
    have habc := adjacent_color_ne R hab
    have hbtc := adjacent_color_ne R hbt
    cases hb : color R b <;> cases hc : color R t <;> simp_all
  have heb : edgeOmega R b ≤ edgeStar R geometry a b := by
    have hb : color R b ≠ false := by simpa only [ha] using (adjacent_color_ne R hab).symm
    have hZb : Z R b = edgeOmega R b := by rw [Z, if_neg hb]
    rw [← hZb]
    exact (edge_Z_le t b htb (adjacent_symm R hbt)).trans
      (le_iSup_of_le t (le_iSup_of_le ⟨ht, hbt⟩ le_rfl))
  rw [Z, if_pos ha]
  apply iSup_le
  intro c
  apply iSup_le
  intro hc
  obtain ⟨g, hg, hgc⟩ := stabilizer_transitive_neighbors R a hab hc
  rw [← hgc, edgeOmega_act]
  exact (map_mono heb).trans (le_iSup (fun k : stabilizer R a =>
    (edgeStar R geometry a b).map (MulAut.conj (k : FreeAmalgam R)).toMonoidHom) ⟨g⁻¹, (stabilizer R a).inv_mem hg⟩)

/-- The identity conjugate includes the edge star in its stabilizer span. -/
theorem edgeStar_le_star (geometry : Geometry R) (a b : Vertex R) :
    edgeStar R geometry a b ≤ VStar R geometry a b := by
  intro x hx
  apply (le_iSup (fun g : stabilizer R a =>
    (edgeStar R geometry a b).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom) 1)
  exact ⟨x, hx, by simp⟩

/-- The starred span is normalized by the actual vertex stabilizer. -/
theorem star_normalized (geometry : Geometry R) (a b : Vertex R) :
    stabilizer R a ≤ normalizer (VStar R geometry a b : Set (FreeAmalgam R)) :=
  le_normalizer_iSup_conjugates _ _

/-- Every noncentral distance-two generator belongs to the starred span of any chosen edge. -/
theorem nu_Z_le_star [Finite M] (geometry : Geometry R) (early : EarlyFacts R geometry)
    (a b t : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (ht : nu R geometry a t) : Z R t ≤ VStar R geometry a b := by
  have hed : (cosetGraph R).edist t a = 2 := by
    rw [← ((cosetGraph_connected R) t a).coe_dist_eq_edist, ht.1]
    rfl
  obtain ⟨c, htc, hac⟩ := (SimpleGraph.edist_eq_two_iff.mp hed).2.2
  obtain ⟨g, hg, hgb⟩ := stabilizer_transitive_neighbors R a
    ((cosetGraph_adj R _ _).mp hac) hab
  have ht' := nu_act geometry early a t ha ⟨g, hg⟩ ht
  have hbt' : Adjacent R b (act R g t) := by
    have hh := (adjacent_act_iff R g c t).mpr
      (adjacent_symm R ((cosetGraph_adj R _ _).mp htc))
    rwa [hgb] at hh
  have hze : Z R (act R g t) ≤ edgeStar R geometry a b :=
    le_iSup_of_le (act R g t) (le_iSup_of_le ⟨ht', hbt'⟩ le_rfl)
  have hz := hze.trans (edgeStar_le_star geometry a b)
  have hmap : (VStar R geometry a b).map (MulAut.conj g⁻¹).toMonoidHom =
      VStar R geometry a b :=
    mem_normalizer_iff_map_conj_eq.mp
      (star_normalized geometry a b ((stabilizer R a).inv_mem hg))
  rw [Z_act, ← hmap] at hz
  exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hz

/-- The radius group is generated by B and the starred span; this is not generation by the core. -/
theorem radius_eq_B_sup_star [Finite M] (geometry : Geometry R)
    (early : EarlyFacts R geometry) (hlarge : 2 < geometry.b R)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    V R a = B R a (geometry.Z_normal a) ⊔ VStar R geometry a b := by
  have hV := geometry.V_local a ha (by rw [geometry.distance_constant a ha]; exact hlarge)
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    by_cases hB : Z R t ≤ B R a (geometry.Z_normal a)
    · exact hB.trans le_sup_left
    have h0 : (cosetGraph R).dist t a ≠ 0 := by
      intro hh
      have he := (cosetGraph_connected R).dist_eq_zero_iff.mp hh
      apply hB
      simpa only [he] using Z_le_B geometry a hV
    have h1 : (cosetGraph R).dist t a ≠ 1 := by
      intro hh
      apply hB
      exact (edge_Z_le a t ha (adjacent_symm R ((cosetGraph_adj R _ _).mp
        (SimpleGraph.dist_eq_one_iff_adj.mp hh)))).trans (Z_le_B geometry a hV)
    have h2 : (cosetGraph R).dist t a = 2 := by omega
    exact (nu_Z_le_star geometry early a b t ha hab ⟨h2, hB⟩).trans le_sup_right
  · apply sup_le _ (star_le_radius geometry a b)
    rw [early.B_eq_center a ha]
    exact map_subtype_le _

/-- The central B-factor contributes no derived commutators to the radius group. -/
theorem derived_le_star_commutator [Finite M] (geometry : Geometry R)
    (early : EarlyFacts R geometry) (hlarge : 2 < geometry.b R)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅V R a, V R a⁆ ≤ ⁅VStar R geometry a b, Q R a⁆ := by
  have hBc : B R a (geometry.Z_normal a) ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
    rw [early.B_eq_center a ha]
    rintro x ⟨z, hz, rfl⟩ y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)
  have hh := commutator_eq_of_centralizing_sup
    (radius_eq_B_sup_star geometry early hlarge a b ha hab).symm hBc
    ((star_le_radius geometry a b).trans (V R a).le_normalizer)
  rw [← hh, commutator_comm]
  exact commutator_mono le_rfl (V_le_Q geometry hlarge a ha)

/-- Conjugation covariance normalizes the moving Z-layer. -/
theorem U_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (U R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (U R a).map (MulAut.conj g).toMonoidHom = U R a
  have hh := U_act R g⁻¹ a
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using hh.symm

/-- The edge bound extends to the full starred span under stabilizer conjugation. -/
theorem star_commutator_le_of_edge (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (a b : Vertex R) (ha : color R a = false)
    (hedge : ⁅edgeStar R geometry a b, Q R a⁆ ≤ U R a) :
    ⁅VStar R geometry a b, Q R a⁆ ≤ U R a := by
  have heQ : edgeStar R geometry a b ≤ Q R a :=
    (edgeStar_le_star geometry a b).trans
      ((star_le_radius geometry a b).trans (V_le_Q geometry hlarge a ha))
  rw [VStar, commutator_iSup_conjugates _ _ _ heQ (Q_normalized R a)]
  exact iSup_conjugates_le_of_le_normalizer _ _ _ hedge (U_normalized a)

/-- The derived equality and edge bound give the starred commutator equality of (4.6.10). -/
theorem star_commutator_eq_U [Finite M] (geometry : Geometry R)
    (early : EarlyFacts R geometry) (hlarge : 2 < geometry.b R)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hderived : ⁅V R a, V R a⁆ = U R a)
    (hedge : ⁅edgeStar R geometry a b, Q R a⁆ ≤ U R a) :
    ⁅VStar R geometry a b, Q R a⁆ = U R a := by
  apply le_antisymm (star_commutator_le_of_edge geometry hlarge a b ha hedge)
  rw [← hderived]
  exact derived_le_star_commutator geometry early hlarge a b ha hab

/-- The three conclusions of the rank-one argument still to be constructed
from the source hypotheses. No theorem here constructs it from those hypotheses. -/
structure RankOneConclusions (R : Subgroup M) (geometry : Geometry R) : Prop where
  radius_derived : ∀ a, color R a = false → ⁅V R a, V R a⁆ = U R a
  core_le_radius : ∀ a, color R a = false → core R a ≤ V R a
  edge_commutator_le : ∀ a b, color R a = false → Adjacent R a b →
    ⁅edgeStar R geometry a b, Q R a⁆ ≤ U R a

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags
