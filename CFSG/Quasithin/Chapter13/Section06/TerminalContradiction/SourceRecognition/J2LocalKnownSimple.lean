module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.J2Containing
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.J2KnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LocalTransport
/-!
# The original J₂ local seed is excluded without embedding callbacks

The full known-simple SQTK hypothesis of the actual line centralizer
supplies the restricted J₂ component lift. The original normalized local
subgroup is therefore an ambient C-component, and its direct three- and
five-rank isolation feeds the terminal quadratic-ratio contradiction.

The second theorem starts with the actual component of the central omega
centralizer. Its faithful inclusion into the singular centralizer preserves
the J₂ quotient and the literal ambient image. This closes the J₂ branch
of the original 13.6.27 seed construction, with neither A.3.12 nor 5.2.3
as an additional premise.
Source: Aschbacher–Smith 13.6.27, printed pp.934–935.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
open Components.CandidateSelection
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The normalized local J₂ branch in the literal original line centralizer. -/
theorem terminal_contradiction_of_A5_local_j2_knownSimple
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {B : Subgroup (centralizer (V₁ : Set G))}
    (hB : B ∈ Chapter1.L (centralizer (V₁ : Set G))
      ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))))
    (hn : (T : Subgroup G).subgroupOf (centralizer (V₁ : Set G)) ≤ normalizer (B : Set _))
    (e : (B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  have hTC : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
    d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  let S := T.subtype hTC
  have hH := SourceAbelian.point_centralizer_mem_family d houtside
  have hsq := Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple
      ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G))) := by
    refine ⟨?_, hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  have hb := ChapterA.Section03.SourceEmbeddings.Exceptional.jankoTwo_local_isCComponent_normal
    hQ S hB hn ⟨e⟩
  exact terminal_contradiction_of_A5_j2_knownSimple d hCv houtside hcounter hb.1 e

/-- The actual central-omega J₂ seed is excluded in the original context,
retaining its faithful subgroup map into the singular centralizer. -/
theorem terminal_contradiction_of_A5_omega_j2_knownSimple
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {KZ : Subgroup (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))}
    (hKZ : KZ.IsCComponent)
    (e : (KZ ⧸ pCore 2 KZ) ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  let C := centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)
  let D := centralizer (V₁ : Set G)
  obtain ⟨B, hB, hn, _, he⟩ :=
    exists_normalized_local_candidate_in_singular_centralizer d KZ hKZ (Or.inl ⟨e⟩)
  let j : B ≃* KZ :=
    (B.equivMapOfInjective D.subtype D.subtype_injective).trans
      ((MulEquiv.subgroupCongr he).trans
        (KZ.equivMapOfInjective C.subtype C.subtype_injective).symm)
  let q := QuotientGroup.congr (pCore 2 B) (pCore 2 KZ) j (pCore_map_iso 2 j)
  exact terminal_contradiction_of_A5_local_j2_knownSimple d hCv houtside hcounter hB hn (q.trans e)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
