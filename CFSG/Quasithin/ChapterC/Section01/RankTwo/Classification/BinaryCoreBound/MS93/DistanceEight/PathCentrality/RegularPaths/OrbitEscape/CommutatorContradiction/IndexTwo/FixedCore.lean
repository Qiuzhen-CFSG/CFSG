module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo.Noncontainment
public import Theory.GroupTheory.Commutator.NilpotentSaturation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Transport


/-!
# The fixed-core bounds for R₁ in MS93 (4.4.2)

The forward commutator lies in D_a by (4.4.1)(ii), since its displacement
centralizes Vδ while Vδ acts nontrivially on U_a. A commutator of a local
orbit span lying in the center's fixed core already lies in the origin's
natural subgroup: replace each local conjugator by a residual element,
which fixes that commutator pointwise. This proves the forward Z_(a+2)
bound and R₁ ≤ U_a, the latter using (4.4.1)(i) at (a,(a+2)^g).

A separate small-displacement calculation puts [Z_a,Vδ] inside Dδ. This
proves the fixed-core implication in the order-four branch without using
or reproving its independent natural fixed-space identity. The established
reverse-span obstruction now gives R₁ ≠ 1 and R₁ not contained in Dδ.

The conjugate noncommutation is not asserted here. Its exact remaining
geometric premise is Vδ not contained in Q_(a+2)^g, as the final equivalence
shows. The retained turn equation only supplies the local distance bound.

The small-displacement argument follows the private helpers in
CommutatorContradiction.SecondCommutator, specialized here to the actual
start-radius commutator. All conjugations use the source right action.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1)--(4.4.2), printed pp.890--893.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
private theorem small_not_cover_natural
    (common : CommonFacts R source geometry) {c : Vertex R} (hc : color R c = false)
    {K : Subgroup (FreeAmalgam R)} (hK : K ≤ stabilizer R c) (hcard : Nat.card K ≤ 4) :
    ¬ Z R c ≤ K ⊔ fixedCore R c := by
  let S := stabilizer R c
  let D := (fixedCore R c).subgroupOf S
  let U₀ := (U R c).subgroupOf S
  let K₀ := K.subgroupOf S
  let := finite_stabilizer R c
  let : D.Normal := fixedCore_normal R c
  have hUS : U R c ≤ S := (MS93.U_le_Z _).trans (Z_le_stabilizer R c)
  have hDS : fixedCore R c ≤ S := fun _ hx => hx.1.1
  have hUD : U₀ ⊓ D = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    exact (Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) c hc).le
      ⟨hx.1, hx.2.2⟩
  have hUcard : Nat.card U₀ = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUS).toEquiv).trans
      (common.natural.card_at c hc)
  have hKcard : Nat.card K₀ ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv]
    exact hcard
  have hindex : D.relIndex U₀ = 8 := by
    rw [← inf_relIndex_left, hUD, relIndex_bot_left, hUcard]
  intro h
  have hle : U₀ ≤ K₀ ⊔ D := by
    rw [← subgroupOf_sup hK hDS]
    exact comap_mono ((MS93.U_le_Z _).trans h)
  have hh := relIndex_le_of_le_right hle
    (show D.relIndex (K₀ ⊔ D) ≠ 0 from index_ne_zero_of_finite)
  rw [hindex, relIndex_sup_right] at hh
  have hsmall := Nat.le_of_dvd (show 0 < Nat.card K₀ from Nat.card_pos)
    (relIndex_dvd_card D K₀)
  omega

private theorem small_radius_displacement_le_fixed
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    {c : Vertex R} (hc : color R c = false)
    {A K : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R c)
    (hK : K ≤ stabilizer R c) (hcard : Nat.card K ≤ 4)
    (hbound : ⁅V R c, A⁆ ≤ K) : ⁅V R c, A⁆ ≤ fixedCore R c := by
  have hQn : Q R c ≤ normalizer (fixedCore R c : Set (FreeAmalgam R)) :=
    (show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (fixedCore_normalized R c)
  suffices hV : V R c ≤ commutatorPreimage (Q R c) A (fixedCore R c) from
    (commutator_mono hV le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hQn)
  apply (V_le_iff R hc _).mpr
  intro d hd hdist
  have hdQ : Z R d ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    exact lt_of_le_of_lt hdist common.large_distance
  apply le_commutatorPreimage hdQ
  by_cases hdc : d = c
  · subst d
    exact (commutator_mono le_rfl hA).trans_eq (geometry.centralizes c hc) |>.trans bot_le
  have hdist2 : (cosetGraph R).dist d c = 2 := by
    have hpos := (cosetGraph_connected R).pos_dist_of_ne hdc
    have hnot1 : (cosetGraph R).dist d c ≠ 1 := by
      intro h1
      have hadj := (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp h1)
      exact adjacent_color_ne R hadj (hd.trans hc.symm)
    omega
  by_cases hinit : ⁅Z R d, Q R c⁆ ≤ fixedCore R c
  · exact (commutator_mono le_rfl hA).trans hinit
  apply commutator_le.mpr
  intro z hz x hx
  have hs : ⁅localZSpan R d c, zpowers x⁆ ≤ fixedCore R c := by
    by_contra hn
    have hh := (hlocal d c hd hc hdist2 hinit).2 x (hA hx) hn
    apply small_not_cover_natural common hc hK hcard
    apply hh.trans
    apply sup_le_sup_right
    rw [commutator_comm]
    exact (commutator_mono (localZSpan_le_V R hdist2.le) (zpowers_le.mpr hx)).trans hbound
  exact hs (commutator_mem_commutator (Z_le_localZSpan R d c hz) (mem_zpowers x))


private theorem natural_displacement_small
    (common : CommonFacts R source geometry) {a : Vertex R} (ha : color R a = false)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R a)
    (hUA : U R a ≤ normalizer A) (hAp : IsPGroup 2 A) :
    Nat.card (⁅Z R a, A⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  have hn := hA.trans (U_normalized a)
  have heq : ⁅Z R a, A⁆ = ⁅U R a, A⁆ := by
    rw [commutator_comm (Z R a), commutator_comm (U R a)]
    exact (commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans ((naturalStructure common).decomposition_at a ha).symm)
      (inf_le_right.trans (centralizer_le hA))
      hUA).symm
  let := geometry.U_elementary (by have hh := common.large_distance; omega) a ha
  have hUp := IsElementaryAbelian.isPGroup 2 (U R a)
  let := finite_stabilizer R a
  have hUS : U R a ≤ stabilizer R a := (MS93.U_le_Z a).trans (Z_le_stabilizer R a)
  let : Finite (U R a ⊔ A : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (sup_le hUS hA)) (inclusion_injective _)
  let : Finite (U R a) := Finite.of_injective (inclusion hUS) (inclusion_injective _)
  have hne : ⁅U R a, A⁆ ≠ U R a := by
    intro he
    have hb : U R a ≤ ⊥ := le_of_le_sup_commutator_of_isNilpotent
      (U R a ⊔ A) (U R a) ⊥ A (hUp.to_sup_of_normal_left' hAp hn).isNilpotent
      le_sup_left bot_le le_sup_right le_normalizer_of_normal (by simp [he])
    have hc := common.natural.card_at a ha
    rw [le_bot_iff.mp hb, card_bot] at hc
    omega
  have hle : ⁅U R a, A⁆ ≤ U R a := le_normalizer_iff_commutator_le_left.mp hn
  have hlt : Nat.card (⁅U R a, A⁆ : Subgroup (FreeAmalgam R)) < 8 := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge hle (by rwa [common.natural.card_at a ha]))
  have hdvd := card_dvd_of_le hle
  rw [common.natural.card_at a ha] at hdvd
  have hm := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rw [heq]
  omega


private theorem residual_turn (source : LocalSource L R)
    {a c d : Vertex R} (hc : color R c = false)
    (hca : (cosetGraph R).dist c a = 2)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hturn : act R g d = a) :
    ∃ l ∈ Ltilde R c, act R l d = a := by
  have hprod : g ∈ Ltilde R c ⊔ Q R c := (source.local_generation c hc).ge hg
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    ((Ltilde_le_stabilizer c).trans (Q_normalized R c))] at hprod
  obtain ⟨l, hl, q, hq, he⟩ := hprod
  have hqa : act R q⁻¹ a = a :=
    (stabilizer R a).inv_mem (Q_le_stabilizer_of_dist_two R c a hc hca hq)
  refine ⟨l, hl, ?_⟩
  have hh := congrArg (act R q⁻¹) hturn
  rw [← he, act_mul, ← act_mul, mul_inv_cancel, act_one, hqa] at hh
  exact hh

private theorem fixed_span_displacement_le_natural
    (common : CommonFacts R source geometry)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    {A : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R c)
    (hfixed : ⁅localZSpan R a c, A⁆ ≤ fixedCore R c) :
    ⁅localZSpan R a c, A⁆ ≤ U R a := by
  have hQU : Q R c ≤ normalizer (U R a) :=
    (Q_le_stabilizer_of_dist_two R c a hc (by rwa [SimpleGraph.dist_comm])).trans
      (U_normalized a)
  suffices hh : localZSpan R a c ≤ commutatorPreimage (Q R c) A (U R a) from
    (commutator_mono hh le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hQU)
  apply iSup_le
  intro g
  have hgc : act R g c = c := g.property
  have hdist : (cosetGraph R).dist (act R g a) c = 2 := by
    simpa only [hgc, hd] using dist_act R (g : FreeAmalgam R) a c
  obtain ⟨l, hl, hla⟩ := residual_turn source hc
    (by rw [SimpleGraph.dist_comm]; exact hdist) g.property rfl
  have hZQ : Z R (act R g a) ≤ Q R c :=
    (le_iSup (fun k : stabilizer R c => Z R (act R k a)) g).trans
      (localZSpan_le_Q R hc hd.le common.large_distance)
  apply le_commutatorPreimage hZQ
  have hD : ⁅Z R (act R g a), A⁆ ≤ fixedCore R c :=
    (commutator_mono (le_iSup (fun k : stabilizer R c => Z R (act R k a)) g)
      le_rfl).trans hfixed
  have hU : ⁅Z R (act R g a), A⁆ ≤ U R (act R g a) :=
    (commutator_mono le_rfl (hA.trans
      (Q_le_stabilizer_of_dist_two R c _ hc (by rw [SimpleGraph.dist_comm]; exact hdist)))).trans_eq
        (Escape.Initial.Z_commutator_stabilizer source _ ((action_preserves_color R g a).trans ha))
  intro x hx
  have hxD := hD hx
  have hxU := hU hx
  rw [← hla, U_act] at hxU
  obtain ⟨y, hy, he⟩ := hxU
  have hfix : (MulAut.conj l⁻¹) x = x := by
    change l⁻¹ * x * (l⁻¹)⁻¹ = x
    rw [hxD.2 l⁻¹ ((Ltilde R c).inv_mem hl), mul_inv_cancel_right]
  have hyx : y = x := (MulAut.conj l⁻¹).injective (he.trans hfix.symm)
  exact hyx ▸ hy

omit [Finite M] in
private theorem span_intersection_fixed
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) :
    ⁅localZSpan R a c, Q R a ⊓ Q R c⁆ ≤ fixedCore R c := by
  by_cases h : ⁅Z R a, Q R c⁆ ≤ fixedCore R c
  · exact (commutator_mono le_rfl inf_le_right).trans
      ((LocalCommutator.span_commutator_le_fixed_iff hc hd.le common.large_distance).mpr h)
  · exact (hlocal a c ha hc hd h).1

namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

/-- The entire start-radius displacement lies in Dδ. Its order is at most four:
a finite two-group cannot act with full displacement on the natural eight.
Clause (4.4.1)(ii) then excludes covering Zδ modulo its disjoint fixed core. -/
theorem start_radius_commutator_le_delta_fixed (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R) :
    ⁅Z R a, V R s.delta⁆ ≤ fixedCore R s.delta := by
  have hZa : Z R a ≤ Q R s.delta := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a p.start_color)
    rw [geometry.distance_constant a p.start_color, SimpleGraph.dist_comm, s.distance_start hb]
    change geometry.b R - 2 < geometry.b R
    omega
  have hVa : V R s.delta ≤ stabilizer R a := s.radius_le_start_stabilizer hb
  let := s.radius_elementary hb
  have hcard := natural_displacement_small common p.start_color (V R s.delta) hVa
    (((MS93.U_le_Z a).trans hZa).trans
      ((show Q R s.delta ≤ stabilizer R s.delta from fun _ hx => hx.1).trans
        (MS93.V_normalized s.delta)))
    (IsElementaryAbelian.isPGroup 2 (V R s.delta))
  have hK : ⁅Z R a, V R s.delta⁆ ≤ stabilizer R s.delta :=
    (commutator_mono hZa ((geometry.V_le_Q (by omega)) s.delta s.delta_color)).trans
      (commutator_le_self _ ) |>.trans (fun _ hx => hx.1)
  have hh := small_radius_displacement_le_fixed common hlocal s.delta_color hZa hK hcard
    (show ⁅V R s.delta, Z R a⁆ ≤ ⁅Z R a, V R s.delta⁆ by rw [commutator_comm])
  rwa [commutator_comm] at hh

/-- The fixed-core implication required in the index-four branch. In fact the
explicit commutator containment suffices, so no image-order premise is needed. -/
theorem firstCommutator_le_delta_fixed_of_le_commutator (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R)
    (hcomm : s.firstCommutator ≤ ⁅Z R a, V R s.delta⁆) :
    s.firstCommutator ≤ fixedCore R s.delta :=
  hcomm.trans (s.start_radius_commutator_le_delta_fixed hb common hlocal)


omit [Finite M] in
private theorem delta_Z_le_conjugate_kernel (s : Configuration p)
    (hb : 4 < geometry.b R) : Z R s.delta ≤ Q R s.conjugateSecond := by
  apply Z_le_Q_of_dist_lt R s.delta (geometry.exists_critical _ s.delta_color)
  rw [geometry.distance_constant _ s.delta_color, SimpleGraph.dist_comm]
  change (cosetGraph R).dist s.conjugateSecond s.delta < geometry.b R
  exact lt_of_le_of_lt (s.conjugateSecond_distance hb) (by omega)

/-- The printed forward commutator bound. Clause (4.4.1)(ii) first puts the
commutator in D_a: otherwise it would force Vδ to centralize the natural U_a.
Residual conjugation then places it in U_(a+2), hence in Z_(a+2). -/
theorem forwardSpan_commutator_le_second_Z (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R) :
    ⁅localZSpan R (p.walk.getVert 2) a, Z R s.delta⁆ ≤ Z R (p.walk.getVert 2) := by
  have hl := p.length_eq_b
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph R).dist (p.walk.getVert 2) a = 2 := by
    rw [SimpleGraph.dist_comm, p.dist_start (by omega)]
  let W := localZSpan R (p.walk.getVert 2) a
  have hWQ : W ≤ Q R a := localZSpan_le_Q R p.start_color hd.le common.large_distance
  have hWS : W ≤ stabilizer R s.delta :=
    (localZSpan_le_V R hd.le).trans (s.start_radius_le_delta_stabilizer hb)
  have hDnorm : Q R a ≤ normalizer (fixedCore R a) :=
    (show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (fixedCore_normalized R a)
  have hDS : ⁅fixedCore R a, V R s.delta⁆ ≤ fixedCore R a :=
    le_normalizer_iff_commutator_le_left.mp
      ((s.radius_le_start_stabilizer hb).trans (fixedCore_normalized R a))
  have hfixed : ⁅W, Z R s.delta⁆ ≤ fixedCore R a := by
    by_cases hinit : ⁅Z R (p.walk.getVert 2), Q R a⁆ ≤ fixedCore R a
    · exact (commutator_mono le_rfl (s.delta_Z_le_start_kernel hb)).trans
        ((LocalCommutator.span_commutator_le_fixed_iff p.start_color hd.le
          common.large_distance).mpr hinit)
    let := s.radius_elementary hb
    have hVV : V R s.delta ≤ centralizer (V R s.delta : Set (FreeAmalgam R)) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    apply commutator_le.mpr
    intro z hz x hx
    have hWX : ⁅W, zpowers x⁆ ≤ fixedCore R a := by
      by_contra hn
      have hcover := (hlocal _ _ hc p.start_color hd hinit).2 x
        (s.delta_Z_le_start_kernel hb hx) hn
      have hKQ : ⁅zpowers x, W⁆ ≤ Q R a :=
        (commutator_mono (zpowers_le.mpr (s.delta_Z_le_start_kernel hb hx)) hWQ).trans
          (commutator_le_self _)
      have hKV : ⁅zpowers x, W⁆ ≤ V R s.delta :=
        (commutator_mono (zpowers_le.mpr (Z_le_VBall R s.delta 2 hx)) le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp (hWS.trans (MS93.V_normalized s.delta)))
      have hKzero : ⁅⁅zpowers x, W⁆, V R s.delta⁆ = ⊥ :=
        commutator_eq_bot_iff_le_centralizer.mpr (hKV.trans hVV)
      have hpre : Z R a ≤ commutatorPreimage (Q R a) (V R s.delta) (fixedCore R a) :=
        hcover.trans (sup_le (le_commutatorPreimage hKQ (hKzero.le.trans bot_le))
          (le_commutatorPreimage inf_le_left hDS))
      have hCD : ⁅Z R a, V R s.delta⁆ ≤ fixedCore R a :=
        (commutator_mono hpre le_rfl).trans
          (commutator_commutatorPreimage_le _ _ _ hDnorm)
      have hCU : ⁅Z R a, V R s.delta⁆ ≤ U R a :=
        (commutator_mono le_rfl (s.radius_le_start_stabilizer hb)).trans_eq
          (Escape.Initial.Z_commutator_stabilizer source a p.start_color)
      apply s.start_commutator_ne_bot hb common
      apply le_bot_iff.mp
      rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) a p.start_color]
      exact le_inf hCU (hCD.trans inf_le_right)
    exact hWX (commutator_mem_commutator hz (mem_zpowers x))
  exact (fixed_span_displacement_le_natural common hc p.start_color hd
    (s.delta_Z_le_start_kernel hb) hfixed).trans (MS93.U_le_Z _)

/-- The literal R₁ lies in U_a. Both endpoint kernels contain Zδ, so
(4.4.1)(i) puts its displacement in D_(a+2)^g. The fixed span calculation
removes the residual conjugates of Z_a, retaining its actual natural summand. -/
theorem firstCommutator_le_start_natural (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R) : s.firstCommutator ≤ U R a := by
  have hl := p.length_eq_b
  have hga : act R s.g a = a := s.mem_stabilizer
  have hc : color R s.conjugateSecond = false :=
    (action_preserves_color R s.g _).trans
      ((p.vertex_color (by omega)).mpr (by decide))
  have hd : (cosetGraph R).dist a s.conjugateSecond = 2 := by
    change (cosetGraph R).dist a (act R s.g (p.walk.getVert 2)) = 2
    simpa only [hga, p.dist_start (by omega : 2 ≤ p.walk.length)] using
      dist_act R s.g a (p.walk.getVert 2)
  have hspan : (localZSpan R a (p.walk.getVert 2)).map (MulAut.conj s.g⁻¹).toMonoidHom =
      localZSpan R a s.conjugateSecond := by
    rw [← LocalCommutator.CriticalCase.localZSpan_act, hga]
    rfl
  have hZ : Z R s.delta ≤ Q R a ⊓ Q R s.conjugateSecond :=
    le_inf (s.delta_Z_le_start_kernel hb) (s.delta_Z_le_conjugate_kernel hb)
  have hD : ⁅localZSpan R a s.conjugateSecond, Z R s.delta⁆ ≤ fixedCore R s.conjugateSecond :=
    (commutator_mono le_rfl hZ).trans (span_intersection_fixed common hlocal p.start_color hc hd)
  rw [firstCommutator, hspan]
  exact fixed_span_displacement_le_natural common p.start_color hc hd
    (s.delta_Z_le_conjugate_kernel hb) hD


/-- Discharge the forward-bound premise of the established reverse-span obstruction. -/
theorem firstCommutator_not_le_second_Z (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    ¬ s.firstCommutator ≤ Z R (p.walk.getVert 2) :=
  s.firstCommutator_not_le_second_Z_of_forward_bound hb common hnorm
    (s.forwardSpan_commutator_le_second_Z hb common hlocal)

/-- The actual R₁ is nontrivial under joint normality. -/
theorem firstCommutator_ne_bot (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) : s.firstCommutator ≠ ⊥ :=
  s.firstCommutator_ne_bot_of_forward_bound hb common hnorm
    (s.forwardSpan_commutator_le_second_Z hb common hlocal)

/-- Joint normality excludes R₁ from Dδ, since it is nontrivial in Uδ. -/
theorem firstCommutator_not_le_delta_fixed (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    ¬ s.firstCommutator ≤ fixedCore R s.delta :=
  s.firstCommutator_not_le_delta_fixed_of_forward_bound hb common hnorm
    (s.forwardSpan_commutator_le_second_Z hb common hlocal)

/-- The exact remaining geometric escape needed for conjugate noncommutation.
The common natural marking identifies the kernel in the actual conjugate
stabilizer; this equivalence does not assert that the escape has been proved. -/
theorem conjugate_noncommutation_iff_radius_not_le_kernel (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry) :
    ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥ ↔ ¬ V R s.delta ≤ Q R s.conjugateSecond := by
  have hc : color R s.conjugateSecond = false :=
    (action_preserves_color R s.g _).trans
      ((p.vertex_color (by have hl := p.length_eq_b; omega)).mpr (by decide))
  have heq : ⁅Z R s.conjugateSecond, V R s.delta⁆ = ⊥ ↔
      V R s.delta ≤ Q R s.conjugateSecond := by
    constructor
    · intro hh
      rw [← common.natural.centralizer s.conjugateSecond hc]
      exact le_inf (s.radius_le_conjugateSecond_stabilizer hb)
        ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)).trans
          (centralizer_le (MS93.U_le_Z _)))
    · intro hh
      exact le_bot_iff.mp ((commutator_mono le_rfl hh).trans_eq
        (geometry.centralizes _ hc))
  exact not_congr heq

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
