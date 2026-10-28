module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredSolvableAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.AugmentationSelectionAt

/-!
# The original fixed-module application of covered solvable exclusion

Construct Hypothesis 12.2.3 and the five-dimensional CoreMarking from the
original Hypothesis 13.3.1, chosen module and earlier 13.3.2 fixed-module
clause. A solvable escaping centralizer forces the literal quotient
L/O₂(L) to be ordinary A₆. Conversely, in the covered row every escaping
weight has a nonsolvable centralizer and hence an actual relatively normal
escaping component. The final application constructs such a point from
12.2.13 at the same G,T; no point, marking or component is supplied.

These are the ordinary/nonsolvable inputs needed by the remaining guarded
recognition assembly. They do not assert Sp₆(2), discharge earlier source
inputs or transfer nonsolvability between two chosen points.
Source: Aschbacher--Smith 13.4.1, 13.4.5 and 13.4.8, pp.896--897,904--905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable Nonsolvable
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Both original quotient rows are considered: solvability of an escaping
centralizer excludes the covered row and yields the actual ordinary quotient. -/
theorem augmentation_solvable_initial_quotient_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G))) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  rcases original_quotient_rows D m h.quasisimple with ho | hc
  · exact ho
  · exact (covered_solvable_escape_impossible_at h₀ h structural D m hc z hz hzL hout hsolv).elim

/-- Apply the solvable row selection to the original chosen module. Its
marking and Chapter 12 applicability are constructed from preceding 13.3.2. -/
theorem original_solvable_initial_quotient_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G))) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  exact augmentation_solvable_initial_quotient_at h₀ h structural D m z hz hzL hout hsolv

/-- In the covered original row, each escaping weight has an actual escaping
component. Nonsolvability is proved separately for that very point. -/
theorem original_covered_escaping_component_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    ¬ Group.IsSolvable (centralizer ({z.val} : Set G)) ∧
      ∃ K : Subgroup G,
        K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
        K ∈ MainForward.faithfulLocalComponents T ∧
        K ∈ Chapter1.LStar G T ∧
        centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
        (T : Subgroup G) ≤ normalizer (K : Set G) ∧
        ¬ K ≤ normalizer (L : Set G) ∧
        ¬ L ≤ normalizer (K : Set G) := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  have hn := covered_solvable_escape_impossible_at h₀ h structural D m hc z hz hzL hout
  exact ⟨hn,augmentation_exists_escaping_component_at h₀ h structural m h1332 hz
    (fun he => hzL (he ▸ one_mem _)) hout hn⟩

/-- The original covered fixed-module hypotheses construct an escaping point
and a relatively normal component, with all source guards at this same G,T. -/
theorem original_covered_exists_escaping_component_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) :
    ∃ (z : V) (K : Subgroup G), z ≠ 1 ∧
      z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
      z.val ∉ centralizer (L : Set G) ∧
      ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) ∧
      ¬ Group.IsSolvable (centralizer ({z.val} : Set G)) ∧
      K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      K ∈ Chapter1.LStar G T ∧
      centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      ¬ L ≤ normalizer (K : Set G) := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  obtain ⟨z,hz1,hz,hzL,hout⟩ := exists_nonfixed_omega_escape_at h₀ h structural D m earlier
  obtain ⟨hn,K,hK⟩ := original_covered_escaping_component_at h₀ D hfixed structural h1332
    fixed hc z hz hzL hout
  exact ⟨z,K,hz1,hz,hzL,hout,hn,hK⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
