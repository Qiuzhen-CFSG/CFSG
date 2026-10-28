module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical.Controls
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# Small radius displacement at the actual MS93 endpoint actors

The marked natural eight is disjoint from the fixed core, so a subgroup
of order at most four in the stabilizer cannot cover it modulo that core.
For actors contained in an endpoint Z-layer, movement at distance b-2 gives
the needed critical escape; at shorter distance there is full commutation.

The applications use Z_a and Z_(a+2)^g with the original R₁/R₂ subgroups.
The separate conjugate noncommutation remains an independent calculation.
Only the earlier nonnatural-section exclusion on critical prefixes is assumed.

Source: MS93 (4.4.1)--(4.4.2), printed pp.890--893.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open LocalCommutator
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- A subgroup of order at most four cannot cover the natural eight modulo
the fixed core. The small subgroup need only lie in the local stabilizer. -/
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

/-- At a source endpoint actor, a displacement of order at most four lies
in the fixed core. At shorter distance the whole radius group commutes;
at distance b-2, actual movement supplies the critical escape witness. -/
theorem small_radius_displacement_le_fixed_of_endpoint
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (exclude : CriticalPrefixExclusion R geometry)
    {c e : Vertex R} (hc : color R c = false) (he : color R e = false)
    (hdist : (cosetGraph R).dist c e + 2 ≤ geometry.b R)
    {A K : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R c) (hAZ : A ≤ Z R e)
    (hK : K ≤ stabilizer R c) (hcard : Nat.card K ≤ 4)
    (hbound : ⁅V R c, A⁆ ≤ K) : ⁅V R c, A⁆ ≤ fixedCore R c := by
  by_cases hstrict : (cosetGraph R).dist c e + 2 < geometry.b R
  · have hzero : ⁅Q R e, Z R e⁆ = ⊥ := by
      rw [commutator_comm]
      exact geometry.centralizes e he
    exact ((commutator_mono (V_le_Q_of_dist_add_two_lt R hc hstrict) hAZ).trans_eq
      hzero).trans bot_le
  have hdist_eq : (cosetGraph R).dist c e + 2 = geometry.b R := by omega
  have hQn : Q R c ≤ normalizer (fixedCore R c : Set (FreeAmalgam R)) :=
    (show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (fixedCore_normalized R c)
  suffices hV : V R c ≤ commutatorPreimage (Q R c) A (fixedCore R c) from
    (commutator_mono hV le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hQn)
  apply (V_le_iff R hc _).mpr
  intro d hd hnear
  have hdQ : Z R d ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    exact lt_of_le_of_lt hnear common.large_distance
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
  apply commutator_le.mpr
  intro z hz x hx
  have hs : ⁅localZSpan R d c, zpowers x⁆ ≤ fixedCore R c := by
    by_contra hn
    have hh := (LocalCommutator.SourceCritical.localControl_of_endpoint_movement
      common hb exclude hd hc hdist2 he hdist_eq (hA hx) (hAZ hx) hn).2 x (hA hx) hn
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

open CommutatorContradiction
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

/-- The R₁ radius application has the literal actor Z_a, at distance b-2
from delta. This discharges the fixed-core implication in its index-four case. -/
theorem start_radius_commutator_le_delta_fixed
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (exclude : CriticalPrefixExclusion R geometry) (s : Configuration p) :
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
  have hh := small_radius_displacement_le_fixed_of_endpoint common hb exclude
    s.delta_color p.start_color (by rw [s.distance_start hb]; omega)
    hZa le_rfl hK hcard
    (show ⁅V R s.delta, Z R a⁆ ≤ ⁅Z R a, V R s.delta⁆ by rw [commutator_comm])
  rwa [commutator_comm] at hh

/-- The R₂ radius application retains its original small subgroup R₂.
The conjugate endpoint may be closer than b-2; that branch is full commutation.
The separate noncommutation and containment arguments remain independent. -/
theorem conjugate_commutator_le_fixed_of_le_second
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (exclude : CriticalPrefixExclusion R geometry) (s : Configuration p)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ fixedCore R s.delta := by
  have hc : color R s.conjugateSecond = false :=
    (action_preserves_color R s.g _).trans
      ((p.vertex_color (by have hl := p.length_eq_b; omega)).mpr (by decide))
  have hd : (cosetGraph R).dist s.delta s.conjugateSecond + 2 ≤ geometry.b R := by
    rw [SimpleGraph.dist_comm]
    have h := s.conjugateSecond_distance hb
    omega
  rw [commutator_comm] at hbound ⊢
  exact small_radius_displacement_le_fixed_of_endpoint common hb exclude
    s.delta_color hc hd (s.conjugateSecond_Z_le_delta_kernel hb) le_rfl
    ((s.secondCommutator_le_radius hb).trans
      (geometry.V_local s.delta s.delta_color (by
        rw [geometry.distance_constant _ s.delta_color]; exact common.large_distance)))
    (s.secondCommutator_card_le_four hb common) hbound

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical

