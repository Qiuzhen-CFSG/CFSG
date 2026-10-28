module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.InsidePreparation

/-!
# Assembly of the backward selection

The normalizer case is reduced to the precise noncritical-normalization
implication used with (2.1)(vi). The other case retains the fixed-preimage
hypothesis and must be proved by the dual-module and escaping-conjugate
argument of (1.5)--(1.6). These are explicit missing premises, not source
conclusions. The assembly constructs the actual two-edge walk and keeps
the conjugator and the original critical path in the published witness.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (2), p.891.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

/-- Construct the full witness from one local conjugate and its two substantive
noncontainments. The backward walk is an actual shortest graph walk. -/
theorem backwardWitness_of_conjugate {a c e : Vertex R}
    (hd : (cosetGraph R).dist a c = 2) (p : CriticalPath R geometry c e)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hcrit : ¬ Z R (act R g a) ≤ Q R (p.walk.getVert (p.walk.length - 2)))
    (htriple : ⁅⁅Z R (act R g a), Q R c⁆, Z R e⁆ ≠ ⊥) :
    Nonempty (BackwardWitness R geometry a c) := by
  have hfix : act R g c = c := hg
  have hdist : (cosetGraph R).dist (act R g a) c = 2 := by
    rw [← hfix, dist_act]
    exact hd
  obtain ⟨q, hq⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist (act R g a) c
  exact ⟨{
    endpoint := e
    path := p
    backward := act R g a
    conjugator := g
    local_conjugator := hg
    conjugator_image := rfl
    backwardWalk := q
    backward_length := hq.trans hdist
    noncontainment := hcrit
    triple_ne := htriple }⟩

/-- The normalizer selection completes the outside-B case once the source's
noncritical-normalization implication is supplied. -/
theorem exists_backwardWitness_of_outside [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c e : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (p : CriticalPath R geometry c e)
    (hout : ¬ ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    (hcontained : ∀ g ∈ stabilizer R c,
      Z R (act R g a) ≤ Q R (p.walk.getVert (p.walk.length - 2)) →
      Z R e ≤ normalizer (⁅Z R (act R g a), Q R c⁆ ⊔ Z R c : Subgroup (FreeAmalgam R))) :
    Nonempty (BackwardWitness R geometry a c) := by
  obtain ⟨g, hg, hn, htriple⟩ := exists_unnormalized_displacement common hb ha hd p hout
  exact backwardWitness_of_conjugate hd p hg (fun h => hn (hcontained g hg h)) htriple

/-- Final case assembly, retaining both independent source obligations.
This is not an unconditional proof of claim (2). -/
theorem exists_backwardWitness_of_case_inputs [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (hnone : ¬ HasNaturalSection R a c)
    (hcontained : ¬ ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c) →
      ∀ e (p : CriticalPath R geometry c e), ∀ g ∈ stabilizer R c,
      Z R (act R g a) ≤ Q R (p.walk.getVert (p.walk.length - 2)) →
      Z R e ≤ normalizer (⁅Z R (act R g a), Q R c⁆ ⊔ Z R c : Subgroup (FreeAmalgam R)))
    (hinside : ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c) →
      ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c → ¬ HasNaturalSection R a c →
      ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c →
      ∀ e (p : CriticalPath R geometry c e),
      ∃ g ∈ stabilizer R c,
        ¬ Z R (act R g a) ≤ Q R (p.walk.getVert (p.walk.length - 2)) ∧
        ⁅⁅Z R (act R g a), Q R c⁆, Z R e⁆ ≠ ⊥) :
    Nonempty (BackwardWitness R geometry a c) := by
  obtain ⟨e, ⟨p⟩⟩ := CriticalPath.exists_from (geometry := geometry) hc
  by_cases hB : ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c)
  · obtain ⟨g, hg, hcrit, htriple⟩ := hinside hB hn hnone
      (span_triple_le_Z_of_displacement_le_B hc hd.le (by omega) hB) e p
    exact backwardWitness_of_conjugate hd p hg hcrit htriple
  · exact exists_backwardWitness_of_outside common hb ha hd p hB (hcontained hB e p)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
