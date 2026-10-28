module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical.Radius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo

/-!
# The R₁ calculation with critical-prefix local control

The backward critical chain supplies the local pair (a+2,a), and the actual
conjugated path supplies (a,(a+2)^g). The shared endpoint radius calculation
bounds [Z_a,V_delta] in D_delta. These prove the original fixed-core inputs
to the natural index-four exclusion.

The nonzero R₁ separately detects a critical endpoint in the conjugate orbit;
source (4.3) then proves conjugate noncommutation. This premise is proved,
not inferred from the index or assumed in the R₂ application.

Source: MS93 (4.4.2), printed p.893, the R₁ argument.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

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


namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

/-- The fixed-core implication required in the index-four branch. In fact the
explicit commutator containment suffices, so no image-order premise is needed. -/
theorem firstCommutator_le_delta_fixed_of_le_commutator_of_criticalPrefix (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hcomm : s.firstCommutator ≤ ⁅Z R a, V R s.delta⁆) :
    s.firstCommutator ≤ fixedCore R s.delta :=
  hcomm.trans (OrbitEscape.SourceCritical.start_radius_commutator_le_delta_fixed common hb exclude s)


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
theorem forwardSpan_commutator_le_second_Z_of_criticalPrefix (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry) :
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
      have hcover := (OrbitEscape.SourceCritical.backward_prefix_control common hb exclude s hinit).2 x
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
theorem firstCommutator_le_start_natural_of_criticalPrefix (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry) : s.firstCommutator ≤ U R a := by
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
    by
      apply (commutator_mono le_rfl hZ).trans
      by_cases hinit : ⁅Z R a, Q R s.conjugateSecond⁆ ≤ fixedCore R s.conjugateSecond
      · exact (commutator_mono le_rfl inf_le_right).trans
          ((LocalCommutator.span_commutator_le_fixed_iff hc hd.le common.large_distance).mpr hinit)
      · exact (OrbitEscape.SourceCritical.conjugate_prefix_control common hb exclude p
          s.mem_stabilizer hinit).1
  rw [firstCommutator, hspan]
  exact fixed_span_displacement_le_natural common p.start_color hc hd
    (s.delta_Z_le_conjugate_kernel hb) hD


/-- Discharge the forward-bound premise of the established reverse-span obstruction. -/
theorem firstCommutator_not_le_second_Z_of_criticalPrefix (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    ¬ s.firstCommutator ≤ Z R (p.walk.getVert 2) :=
  s.firstCommutator_not_le_second_Z_of_forward_bound hb common hnorm
    (s.forwardSpan_commutator_le_second_Z_of_criticalPrefix hb common exclude)

/-- The actual R₁ is nontrivial under joint normality. -/
theorem firstCommutator_ne_bot_of_criticalPrefix (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) : s.firstCommutator ≠ ⊥ :=
  s.firstCommutator_ne_bot_of_forward_bound hb common hnorm
    (s.forwardSpan_commutator_le_second_Z_of_criticalPrefix hb common exclude)

/-- Joint normality excludes R₁ from Dδ, since it is nontrivial in Uδ. -/
theorem firstCommutator_not_le_delta_fixed_of_criticalPrefix (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    ¬ s.firstCommutator ≤ fixedCore R s.delta :=
  s.firstCommutator_not_le_delta_fixed_of_forward_bound hb common hnorm
    (s.forwardSpan_commutator_le_second_Z_of_criticalPrefix hb common exclude)

/-- Source (4.3) applied to a genuine critical endpoint detected by R₁.
The conjugate vertex is its predecessor at distance two, not a critical
endpoint itself. Joint normality and local control supply R₁ ≠ 1. -/
theorem radius_not_le_conjugate_kernel_of_criticalPrefix (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    ¬ V R s.delta ≤ Q R s.conjugateSecond := by
  have hl := p.length_eq_b
  have hga : act R s.g a = a := s.mem_stabilizer
  have hac : (cosetGraph R).dist a s.conjugateSecond = 2 := by
    change (cosetGraph R).dist a (act R s.g (p.walk.getVert 2)) = 2
    simpa only [hga, p.dist_start (by omega : 2 ≤ p.walk.length)] using
      dist_act R s.g a (p.walk.getVert 2)
  have hspan : (localZSpan R a (p.walk.getVert 2)).map
      (MulAut.conj s.g⁻¹).toMonoidHom = localZSpan R a s.conjugateSecond := by
    rw [← LocalCommutator.CriticalCase.localZSpan_act, hga]
    rfl
  have hnear : (cosetGraph R).dist s.delta s.conjugateSecond ≤ geometry.b R - 2 := by
    rw [SimpleGraph.dist_comm]
    exact s.conjugateSecond_distance hb
  intro htrap
  apply s.firstCommutator_ne_bot_of_criticalPrefix hb common exclude hnorm
  rw [firstCommutator, hspan]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply iSup_le
  intro t
  have htc : act R t s.conjugateSecond = s.conjugateSecond := t.property
  have hdist : (cosetGraph R).dist s.conjugateSecond (act R t a) = 2 := by
    have hh := dist_act R (t : FreeAmalgam R) s.conjugateSecond a
    simpa only [htc, SimpleGraph.dist_comm (u := s.conjugateSecond), hac] using hh
  have hQ : Z R s.delta ≤ Q R (act R t a) := by
    by_contra hn
    have hmin := criticalDistance_le R s.delta (geometry.exists_critical _ s.delta_color) hn
    rw [geometry.distance_constant _ s.delta_color] at hmin
    change geometry.b R ≤ _ at hmin
    have htri := (cosetGraph_connected R).dist_triangle
      (u := s.delta) (v := s.conjugateSecond) (w := act R t a)
    have hcrit : CriticalPair R s.delta (act R t a)
        (geometry.exists_critical _ s.delta_color) := by
      refine ⟨?_, hn⟩
      rw [geometry.distance_constant _ s.delta_color]
      change _ = geometry.b R
      omega
    exact common.escape s.delta s.delta_color (act R t a) hcrit s.conjugateSecond
      hdist (by omega) htrap
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact le_bot_iff.mp ((commutator_mono le_rfl hQ).trans_eq
    (geometry.centralizes _ ((action_preserves_color R t a).trans p.start_color)))

/-- The conjugate noncommutation used in the R₁ argument of MS93 (4.4.2),
with every premise beyond the original fixed-core inputs discharged. -/
theorem conjugate_noncommutation_of_criticalPrefix (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥ :=
  (s.conjugate_noncommutation_iff_radius_not_le_kernel hb common).mpr
    (s.radius_not_le_conjugate_kernel_of_criticalPrefix hb common exclude hnorm)
/-- The actual backward radius has image of order two in Gₐ/Qₐ.
The fixed-core and marked natural-module calculations exclude order four. -/
theorem backward_index_two_of_criticalPrefix (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    (Q R a).relIndex (V R s.delta) = 2 := by
  exact s.backward_index_two_of_R1_controls hb common hnorm
    (s.forwardSpan_commutator_le_second_Z_of_criticalPrefix hb common exclude)
    (s.firstCommutator_le_start_natural_of_criticalPrefix hb common exclude)
    (fun _ hcomm => s.firstCommutator_le_delta_fixed_of_le_commutator_of_criticalPrefix hb common exclude hcomm)
    (s.backward_natural_fixed_le_commutator hb common)

/-- The two R₁ conclusions used by the remaining R₂ source argument,
with no additional index, fixed-space or noncommutation premise. -/
theorem backward_index_two_and_conjugate_noncommutation_of_criticalPrefix (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    (Q R a).relIndex (V R s.delta) = 2 ∧
      ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥ :=
  ⟨s.backward_index_two_of_criticalPrefix hb common exclude hnorm,
    s.conjugate_noncommutation_of_criticalPrefix hb common exclude hnorm⟩

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
