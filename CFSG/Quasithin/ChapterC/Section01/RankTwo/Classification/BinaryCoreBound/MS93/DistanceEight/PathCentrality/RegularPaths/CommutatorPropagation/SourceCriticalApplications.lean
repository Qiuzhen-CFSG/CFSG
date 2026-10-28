module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.SourceCritical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.ActorEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.TerminalDisplacement

/-!
# Regular-path propagation from the source critical-prefix exclusion

The regular turns place the original critical endpoint layers in precisely
those local spans used in the b=6 calculation and the first terminal transport.
Criticality then supplies escape of these spans. The source critical-prefix
version of (4.4.1) gives their commutator bounds; the case of an already fixed
initial displacement is handled directly.

The resulting theorem proves b>6. The terminal-seed theorem derives this bound
and reuses the completed prescribed-orbit, critical-inclusion and terminal-edge
calculations to construct the original four-field TerminalPropagationSeed for
the literal failedSpanCommutator, preserving the relative normalizer and the
inverse conjugation. The final consumer applies the existing actor-based
terminal contradiction and its proved displacement calculation.

The earlier nonnatural-section exclusion on critical prefixes is retained with
qt-c01-ms93-local-commutator-critical-case. The final consumer also retains the
separate BackwardEdgeSwitching source calculation, owned by
qt-c01-ms93-iteration-backward-edge-switch. These results do not prove either
remaining input or the full (4.4) theorem. Existing unrestricted APIs are preserved.

Source: MS93 (4.4.3)--(4.4.4), printed p.894, using (4.4.1), pp.890--892.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.SourceCriticalApplications
open LocalCommutator.NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem span_kernel_intersection_le_fixed
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (exclude : ∀ {d e : Vertex R} (q : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (q.walk.getVert 2)⁆ ≤ fixedCore R (q.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (q.walk.getVert 2) → False)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (escape : SpanEscape geometry a c) :
    ⁅localZSpan R a c, Q R a ⊓ Q R c⁆ ≤ fixedCore R c := by
  by_cases h : ⁅Z R a, Q R c⁆ ≤ fixedCore R c
  · exact (commutator_mono le_rfl inf_le_right).trans
      ((LocalCommutator.span_commutator_le_fixed_iff hc hd.le (by omega)).mpr h)
  · exact (LocalCommutator.SourceCritical.localControl_of_spanEscape
      common hb exclude ha hc hd h escape).1

private theorem six_commutator_le_second_fixed
    (common : CommonFacts R source geometry)
    (exclude : ∀ {d e : Vertex R} (q : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (q.walk.getVert 2)⁆ ≤ fixedCore R (q.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (q.walk.getVert 2) → False)
    {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    (hsix : geometry.b R = 6) : ⁅Z R a, Z R a'⁆ ≤ fixedCore R (p.walk.getVert 2) := by
  have hlen : p.walk.length = 6 := p.length_eq_b.trans hsix
  have hc2 : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hc4 : color R (p.walk.getVert 4) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph R).dist (p.walk.getVert 4) (p.walk.getVert 2) = 2 := by
    rw [SimpleGraph.dist_comm, Iteration.path_distance p (by decide) (by omega)]
  obtain ⟨g, hg, hturn⟩ := hp 2 (by decide) (by decide) (by omega)
  have hturn' : Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 4) = a := by
    simpa only [Nat.reduceAdd, Nat.reduceSub, SimpleGraph.Walk.getVert_zero] using hturn
  have hspan : Z R a ≤ localZSpan R (p.walk.getVert 4) (p.walk.getVert 2) := by
    have hh := le_iSup (fun g : stabilizer R (p.walk.getVert 2) =>
      Z R (Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 4))) ⟨g, hg⟩
    simpa only [hturn', localZSpan] using hh
  have hQ (i : ℕ) (hi : i = 2 ∨ i = 4) : Z R a' ≤ Q R (p.walk.getVert i) := by
    apply Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' p.end_color)
    rw [geometry.distance_constant a' p.end_color, SimpleGraph.dist_comm, p.dist_end i]
    change p.walk.length - i < geometry.b R
    rcases hi with rfl | rfl <;> omega
  have escape : SpanEscape geometry (p.walk.getVert 4) (p.walk.getVert 2) := by
    refine ⟨a', ?_, ?_⟩
    · rw [p.dist_end, hlen, hsix]
    · intro h
      exact p.critical.2 (hspan.trans h)
  exact (commutator_mono hspan (le_inf (hQ 4 (Or.inr rfl)) (hQ 2 (Or.inl rfl)))).trans
    (span_kernel_intersection_le_fixed common (by rw [hsix]; decide) exclude hc4 hc2 hd escape)

/-- MS93 (4.4.3) from the actual regular turns and the earlier critical-prefix
exclusion. Both uses of local commutator control obtain their own escape witness. -/
theorem six_lt (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (exclude : ∀ {d e : Vertex R} (q : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (q.walk.getVert 2)⁆ ≤ fixedCore R (q.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (q.walk.getVert 2) → False)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hp : HasTurnConjugators R p) : 6 < geometry.b R := by
  by_contra! hsmall
  have heven : Even (geometry.b R) := by
    exact geometry.even (alpha R) rfl
  have hsix : geometry.b R = 6 := by
    rw [Nat.even_iff] at heven
    omega
  have hlen : p.walk.length = 6 := p.length_eq_b.trans hsix
  have hfirst := six_commutator_le_second_fixed common exclude p hp hsix
  have hr : HasTurnConjugators R (p.reverse common) :=
    HasTurnConjugators.reverse (R := R) (geometry := geometry) (p := p) common hp
  have hsecond := six_commutator_le_second_fixed (R := R) (geometry := geometry)
    common exclude (p.reverse common) hr hsix
  have hsecond' : ⁅Z R a, Z R a'⁆ ≤ fixedCore R (p.walk.getVert 4) := by
    change ⁅Z R a', Z R a⁆ ≤ fixedCore R (p.walk.reverse.getVert 2) at hsecond
    simpa only [SimpleGraph.Walk.getVert_reverse, hlen, Nat.reduceSub,
      commutator_comm (Z R a') (Z R a)] using hsecond
  obtain ⟨g, hg, hturn⟩ := hp 2 (by decide) (by decide) (by omega)
  have hturn' : Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 4) = a := by
    simpa only [Nat.reduceAdd, Nat.reduceSub, SimpleGraph.Walk.getVert_zero] using hturn
  apply critical_commutator_not_le_fixed common p
  exact (le_inf hfirst hsecond').trans (fixedCore_intersection_le_of_turn source
    ((p.vertex_color (by omega)).mpr (by decide))
    (by rw [SimpleGraph.dist_comm, p.dist_start (by omega)]) hg hturn')

private theorem failedSpanCommutator_le_penultimate_fixed (common : CommonFacts R source geometry)
    (exclude : ∀ {d e : Vertex R} (q : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (q.walk.getVert 2)⁆ ≤ fixedCore R (q.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (q.walk.getVert 2) → False)
    {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 6 < geometry.b R)
    (hp : HasTurnConjugators R p)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    failedSpanCommutator p g ≤ fixedCore R (p.walk.getVert (p.walk.length - 2)) := by
  have hl := p.length_eq_b
  have he : Even p.walk.length := by
    rw [hl]
    exact geometry.even (alpha R) rfl
  have hc : color R (p.walk.getVert (p.walk.length - 2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  have hd : color R (p.walk.getVert (p.walk.length - 4)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  have hdc : (cosetGraph R).dist (p.walk.getVert (p.walk.length - 4))
      (p.walk.getVert (p.walk.length - 2)) = 2 := by
    rw [Iteration.path_distance p (by omega) (Nat.sub_le _ _)]
    omega
  obtain ⟨u, hu, hturn⟩ := hp (p.walk.length - 2)
    ((p.vertex_color (Nat.sub_le _ _)).mp hc) (by omega) (by omega)
  have hturn' : Stellmacher.PushingUp.AmalgamGraph.act R u a' =
      p.walk.getVert (p.walk.length - 4) := by
    simpa only [show p.walk.length - 2 + 2 = p.walk.length by omega,
      show p.walk.length - 2 - 2 = p.walk.length - 4 by omega,
      SimpleGraph.Walk.getVert_length] using hturn
  have hinv : Stellmacher.PushingUp.AmalgamGraph.act R u⁻¹
      (p.walk.getVert (p.walk.length - 4)) = a' := by
    rw [← hturn', ← act_mul, mul_inv_cancel, act_one]
  have hspan : Z R a' ≤ localZSpan R (p.walk.getVert (p.walk.length - 4))
      (p.walk.getVert (p.walk.length - 2)) := by
    have hh := le_iSup (fun k : stabilizer R (p.walk.getVert (p.walk.length - 2)) =>
      Z R (Stellmacher.PushingUp.AmalgamGraph.act R k
        (p.walk.getVert (p.walk.length - 4))))
      ⟨u⁻¹, (stabilizer R _).inv_mem hu⟩
    simpa only [hinv, localZSpan] using hh
  have hW : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 4)) := by
    apply (Seed.transportedSpan_le_radius p (by omega) hg).trans
    apply V_le_Q_of_dist_add_two_lt R p.start_color
    rw [p.dist_start (Nat.sub_le _ _)]
    omega
  have escape : SpanEscape geometry (p.walk.getVert (p.walk.length - 4))
      (p.walk.getVert (p.walk.length - 2)) := by
    refine ⟨a, ?_, ?_⟩
    · rw [SimpleGraph.dist_comm, p.dist_start (Nat.sub_le _ _)]
      omega
    · intro h
      exact (p.reverse common).critical.2 (hspan.trans h)
  change ⁅_, Z R a'⁆ ≤ _
  rw [commutator_comm]
  exact (commutator_mono hspan (le_inf hW hfail)).trans
    (span_kernel_intersection_le_fixed common (by omega) exclude hd hc hdc escape)

/-- Construct the actual source terminal seed under failed prescribed-span escape.
The b>6 bound and both initial prescribed-orbit assertions are proved internally;
only the earlier critical-prefix exclusion remains a local-calculation input. -/
theorem terminal_seed
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (exclude : ∀ {d e : Vertex R} (q : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (q.walk.getVert 2)⁆ ≤ fixedCore R (q.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (q.walk.getVert 2) → False)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {t : Vertex R} (ht : Adjacent R a t)
    (hn : ¬ Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hge : (edgeCommutator R a (p.walk.getVert 1)).map
      (MulAut.conj g⁻¹).toMonoidHom = edgeCommutator R a t)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    TerminalPropagationSeed p (failedSpanCommutator p g) := by
  have hb6 := six_lt common hb exclude p hp
  have hnot := Seed.OrbitGrowth.failedSpanCommutator_not_le_start_Z common p hn hg hge
  have hcrit := Seed.CriticalInclusion.critical_commutator_le_failedSpan common p ht hn hge
  have hedge := Seed.terminal_edge_of_critical_le common p g hfail hnot hcrit
  have hfixed := failedSpanCommutator_le_penultimate_fixed common exclude p hb6 hp hg hfail
  exact ⟨hnot, hedge, hfixed,
    Seed.preceding_edge_of_terminal_and_fixed source p hb6 hp hfixed hedge⟩

/-- Apply the source-specific seed to the existing actor-based terminal consumer.
The literal backward-edge switching remains the independent (4.4.4) source input;
its displacement callback is discharged by the completed terminal calculation. -/
theorem false_of_failed_span_and_backward_switching
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (exclude : ∀ {d e : Vertex R} (q : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (q.walk.getVert 2)⁆ ≤ fixedCore R (q.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (q.walk.getVert 2) → False)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {t : Vertex R} (ht : Adjacent R a t)
    (hn : ¬ Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hge : (edgeCommutator R a (p.walk.getVert 1)).map
      (MulAut.conj g⁻¹).toMonoidHom = edgeCommutator R a t)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hswitch : Iteration.BackwardEdgeSwitching p (failedSpanCommutator p g)) : False := by
  have hb6 := six_lt common hb exclude p hp
  have seed := terminal_seed common hb exclude p hp ht hn hg hge hfail
  exact Iteration.ActorEscape.contradiction_of_local_steps common hb6 exclude p hp seed hswitch
    (Iteration.terminal_displacement common p seed)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.SourceCriticalApplications
