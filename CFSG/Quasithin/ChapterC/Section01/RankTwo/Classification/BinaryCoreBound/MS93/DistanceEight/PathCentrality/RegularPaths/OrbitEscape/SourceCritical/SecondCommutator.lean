module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical.Radius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator.Assembly

/-!
# The R₂ calculation with critical-prefix local control

The forward pair (a+2,a) is a genuine prefix of the reversed backward
critical path. Thus local control applies to the full actor V_delta intersect
Q_a. The separate radius calculation uses the actual conjugate endpoint
Z_(a+2)^g and retains the order-four bound on the literal second commutator.

These two source applications supply the original edge invariance, product
identity and marked radius-quotient recognition arguments. The index-two
image and conjugate noncommutation remain explicit for the R₁ producer.

Source: MS93 (4.4.2), printed p.893, the R₂ argument and final equation.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}
  (s : Configuration p) (hb : 4 < geometry.b R)
include hb

theorem conjugate_commutator_le_fixed_of_le_second_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ fixedCore R s.delta :=
  OrbitEscape.SourceCritical.conjugate_commutator_le_fixed_of_le_second
    common hb exclude s hbound

theorem critical_inf_conjugate_eq_bot_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    ⁅Z R (p.walk.getVert 2), Z R s.delta⁆ ⊓ ⁅Z R s.conjugateSecond, V R s.delta⁆ = ⊥ := by
  apply le_bot_iff.mp
  rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) s.delta s.delta_color]
  exact inf_le_inf (s.critical_commutator_le_delta_natural hb source)
    ((s.conjugate_commutator_le_fixed_of_le_second_of_criticalPrefix hb common exclude hbound).trans inf_le_right)

theorem secondCommutator_eq_critical_sup_conjugate_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    s.secondCommutator =
      ⁅Z R (p.walk.getVert 2), Z R s.delta⁆ ⊔ ⁅Z R s.conjugateSecond, V R s.delta⁆ := by
  let C := ⁅Z R (p.walk.getVert 2), Z R s.delta⁆
  let D := ⁅Z R s.conjugateSecond, V R s.delta⁆
  let E := C ⊔ D
  have hE : E ≤ s.secondCommutator :=
    sup_le (s.critical_commutator_le_secondCommutator hb) hbound
  let := finite_stabilizer R s.delta
  let : Finite s.secondCommutator := Finite.of_injective
    (inclusion ((s.secondCommutator_le_radius hb).trans
      (geometry.V_local s.delta s.delta_color (by
        rw [geometry.distance_constant _ s.delta_color]; exact common.large_distance))))
    (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion hE) (inclusion_injective _)
  have hC : Nat.card C = 2 := s.critical_commutator_card hb common
  have hCD : C ⊓ D = ⊥ := s.critical_inf_conjugate_eq_bot_of_criticalPrefix hb common exclude hbound
  have hne : C ≠ E := by
    intro he
    apply hmove
    apply le_bot_iff.mp
    intro x hx
    exact hCD.le ⟨(show D ≤ C from he ▸ le_sup_right) hx, hx⟩
  have hlarge : 2 < Nat.card E := by
    by_contra! hh
    exact hne (eq_of_le_of_card_ge (show C ≤ E from le_sup_left) (by omega))
  have hdiv : 2 ∣ Nat.card E := hC ▸ card_dvd_of_le (show C ≤ E from le_sup_left)
  have hsmall := s.secondCommutator_card_le_four hb common
  exact (eq_of_le_of_card_ge hE (by omega)).symm

theorem secondCommutator_eq_critical_mul_conjugate_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    (s.secondCommutator : Set (FreeAmalgam R)) =
      (⁅Z R (p.walk.getVert 2), Z R s.delta⁆ : Subgroup (FreeAmalgam R)) *
        (⁅Z R s.conjugateSecond, V R s.delta⁆ : Subgroup (FreeAmalgam R)) := by
  have hcentral : ⁅Z R (p.walk.getVert 2), Z R s.delta⁆ ≤
      centralizer (↑(⁅Z R s.conjugateSecond, V R s.delta⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (s.critical_commutator_le_secondCommutator hb).trans
      ((commutator_eq_bot_iff_le_centralizer.mp (s.secondCommutator_centralizes_radius hb)).trans
        (centralizer_le (hbound.trans (s.secondCommutator_le_radius hb))))
  rw [s.secondCommutator_eq_critical_sup_conjugate_of_criticalPrefix hb common exclude hmove hbound]
  exact coe_mul_of_left_le_normalizer_right _ _
    (hcentral.trans (Subgroup.centralizer_le_normalizer _))

theorem secondCommutator_le_delta_Z_sup_fixed_of_conjugate_le_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta := by
  rw [s.secondCommutator_eq_critical_sup_conjugate_of_criticalPrefix hb common exclude hmove hbound]
  exact sup_le_sup (s.critical_commutator_le_delta_Z hb)
    (s.conjugate_commutator_le_fixed_of_le_second_of_criticalPrefix hb common exclude hbound)

theorem false_of_noncontainment_and_conjugate_natural_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta)
    (hnatural : s.secondCommutator ≤ U R s.conjugateSecond) : False := by
  have hcard := s.secondCommutator_card_four_of_not_le_delta_Z hb common
    (fun h => hnot (h.trans le_sup_left))
  exact hnot (s.secondCommutator_le_delta_Z_sup_fixed_of_conjugate_le_of_criticalPrefix hb common exclude hmove
    (s.conjugate_commutator_le_second_of_natural hb common hcard hnatural))

theorem false_of_noncontainment_and_map_eq_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta)
    (hmap : s.secondCommutator.map (MulAut.conj s.g⁻¹).toMonoidHom = s.secondCommutator) :
    False :=
  s.false_of_noncontainment_and_conjugate_natural_of_criticalPrefix hb common exclude hmove hnot
    (s.secondCommutator_le_conjugate_natural_of_map_eq hb common hmap)

theorem secondCommutator_le_start_fixed_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry) :
    s.secondCommutator ≤ fixedCore R a := by
  have hl := p.length_eq_b
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph R).dist (p.walk.getVert 2) a = 2 := by
    rw [SimpleGraph.dist_comm, p.dist_start (by omega)]
  by_cases hinit : ⁅Z R (p.walk.getVert 2), Q R a⁆ ≤ fixedCore R a
  · exact (commutator_mono le_rfl inf_le_right).trans hinit
  let W := localZSpan R (p.walk.getVert 2) a
  have hWQ : W ≤ Q R a := localZSpan_le_Q R p.start_color hd.le common.large_distance
  have hWS : W ≤ stabilizer R s.delta :=
    (localZSpan_le_V R hd.le).trans (s.start_radius_le_delta_stabilizer hb)
  have hDnorm : Q R a ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) :=
    (show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (fixedCore_normalized R a)
  have hDS : ⁅fixedCore R a, V R s.delta⁆ ≤ fixedCore R a :=
    le_normalizer_iff_commutator_le_left.mp
      ((s.radius_le_start_stabilizer hb).trans (fixedCore_normalized R a))
  let := s.radius_elementary hb
  have hVV : V R s.delta ≤ centralizer (V R s.delta : Set (FreeAmalgam R)) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply commutator_le.mpr
  intro z hz x hx
  have hWX : ⁅W, zpowers x⁆ ≤ fixedCore R a := by
    by_contra hn
    have hcover := (OrbitEscape.SourceCritical.backward_prefix_control common hb exclude s hinit).2 x hx.2 hn
    have hKQ : ⁅zpowers x, W⁆ ≤ Q R a :=
      (commutator_mono (zpowers_le.mpr hx.2) hWQ).trans (commutator_le_self _)
    have hKV : ⁅zpowers x, W⁆ ≤ V R s.delta :=
      (commutator_mono (zpowers_le.mpr hx.1) le_rfl).trans
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
  exact hWX (commutator_mem_commutator (Z_le_localZSpan R _ _ hz) (mem_zpowers x))

theorem secondCommutator_normalized_of_not_le_delta_Z_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta) :
    stabilizer R a ≤ normalizer (s.secondCommutator : Set (FreeAmalgam R)) := by
  have hl := p.length_eq_b
  have ht : color R (p.walk.getVert 1) = true := by
    have hh := p.vertex_color (i := 1) (by omega)
    cases h : color R (p.walk.getVert 1) <;> simp_all
  have hat : Adjacent R a (p.walk.getVert 1) := by
    have hh := p.walk.adj_getVert_succ (i := 0) (by omega)
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj R _ _).mp hh
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  rw [← source.local_generation a p.start_color]
  apply sup_le
  · exact (le_centralizer_iff.mp
      ((s.secondCommutator_le_start_fixed_of_criticalPrefix hb common exclude).trans inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _)
  · rw [s.secondCommutator_eq_first_edge_of_not_le_delta_Z hb common hnot]
    intro g hg
    have hgQ := Q_le_adjacent_h R ht hat hg
    have hgsecond : g ∈ stabilizer R (p.walk.getVert 2) :=
      hgQ.2 _ (adjacent_symm R hct)
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅Z R (p.walk.getVert 2), Q R (p.walk.getVert 1)⁆).map
      (MulAut.conj g).toMonoidHom = _
    have hZ := mem_normalizer_iff_map_conj_eq.mp (Z_normalized R _ hgsecond)
    have hQ := mem_normalizer_iff_map_conj_eq.mp (Q_normalized R _ hgQ.1)
    change (Z R (p.walk.getVert 2)).map (MulAut.conj g).toMonoidHom = _ at hZ
    change (Q R (p.walk.getVert 1)).map (MulAut.conj g).toMonoidHom = _ at hQ
    rw [map_commutator, hZ, hQ]
    rfl

theorem secondCommutator_map_eq_of_not_le_delta_Z_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta) :
    s.secondCommutator.map (MulAut.conj s.g⁻¹).toMonoidHom = s.secondCommutator :=
  mem_normalizer_iff_map_conj_eq.mp
    (s.secondCommutator_normalized_of_not_le_delta_Z_of_criticalPrefix hb common exclude hnot
      ((stabilizer R a).inv_mem s.mem_stabilizer))

theorem false_of_secondCommutator_not_le_delta_Z_sup_fixed_of_criticalPrefix
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta) : False :=
  s.false_of_noncontainment_and_map_eq_of_criticalPrefix hb common exclude hmove hnot
    (s.secondCommutator_map_eq_of_not_le_delta_Z_of_criticalPrefix hb common exclude
      (fun h => hnot (h.trans le_sup_left)))

end Configuration

open Escape.Initial.Natural Escape.Initial.Natural.Splitting
namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

theorem secondCommutator_le_delta_radical_of_criticalPrefix
    (s : Configuration p) (hb : 4 < geometry.b R)
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥) :
    s.secondCommutator ≤ Z R s.delta ⊔ ⁅V R s.delta, Q R s.delta⁆ := by
  by_cases hZ : s.secondCommutator ≤ Z R s.delta
  · exact hZ.trans le_sup_left
  have hcard := s.secondCommutator_card_four_of_not_le_delta_Z hb common hZ
  have hmap := s.secondCommutator_map_eq_of_not_le_delta_Z_of_criticalPrefix hb common exclude hZ
  have hnatural := s.secondCommutator_le_conjugate_natural_of_map_eq hb common hmap
  have hbound := s.conjugate_commutator_le_second_of_natural hb common hcard hnatural
  rw [s.secondCommutator_eq_critical_sup_conjugate_of_criticalPrefix hb common exclude hmove hbound]
  apply sup_le_sup (s.critical_commutator_le_delta_Z hb)
  rw [commutator_comm]
  exact commutator_mono le_rfl (s.conjugateSecond_Z_le_delta_kernel hb)

theorem radius_naturalSection_of_secondCommutator_le_of_criticalPrefix
    (s : Configuration p) (hb : 4 < geometry.b R)
    (common : CommonFacts R source geometry) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hindex : (Q R a).relIndex (V R s.delta) = 2)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hcontain : s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta) :
    Nonempty (Escape.NaturalSectionAt s.delta (V R s.delta) (Z R s.delta)) :=
  s.radius_naturalSection_of_secondCommutator_le_and_radical hb common hindex
    (s.secondCommutator_le_delta_radical_of_criticalPrefix hb common exclude hmove) hcontain

theorem secondCommutator_not_le_delta_Z_sup_fixed_of_criticalPrefix
    (s : Configuration p) (hb : 4 < geometry.b R)
    (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hreverse : ∀ g ∈ stabilizer R a,
      localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4)))
    (hnormal : stabilizer R a ≤ Subgroup.normalizer (OrbitEscape.jointSpan p))
    (hindex : (Q R a).relIndex (V R s.delta) = 2)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥) :
    ¬ s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta := by
  have _ := hreverse
  have _ := hnormal
  intro hcontain
  have hsection := s.radius_naturalSection_of_secondCommutator_le_of_criticalPrefix
    hb common exclude hindex hmove hcontain
  exact s.no_radius_naturalSection_at hb common hforward s.delta_color hsection

theorem false_of_index_two_and_conjugate_noncommutation_of_criticalPrefix
    (s : Configuration p) (hb : 4 < geometry.b R)
    (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hreverse : ∀ g ∈ stabilizer R a,
      localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4)))
    (hnormal : stabilizer R a ≤ Subgroup.normalizer (OrbitEscape.jointSpan p))
    (hindex : (Q R a).relIndex (V R s.delta) = 2)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥) : False := by
  have hnot := s.secondCommutator_not_le_delta_Z_sup_fixed_of_criticalPrefix
    hb common exclude hforward hreverse hnormal hindex hmove
  exact s.false_of_secondCommutator_not_le_delta_Z_sup_fixed_of_criticalPrefix hb common exclude hmove hnot

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
