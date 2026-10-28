module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.SetupCoordinates
public import CFSG.Quasithin.Chapter13.Section06.SourceAbelian.Complete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.OriginalTerminal
public import CFSG.Quasithin.Chapter13.Section02.A5Local.Fusion
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.LocalSource

/-!
# Source parameters on the original A₅ context

The aligned source coordinates retain their literal A₅ quotient action.
Together with the proved normalizer uniqueness, Sylow centralizer identity,
fusion and abelian closure, they construct the entire EarlierA5Setup record
on the original line and marked nonsingular point. Its existing generation
argument then proves 13.6.25 and constructs the initial residual in C_G(V₁).
The large-prime quotient-core exclusion of 13.6.26 is applied to each actual
H_z member, keeping the genuine earlier 13.3.8 input explicit.

The nonsingular centralizer bound, singular-centralizer escape, actual model
exclusions and the full earlier A.3.12 embedding input are still required.
This does not assert the remaining exceptional component classification.
Source: Aschbacher–Smith 13.6.24–27, printed pp.933–935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source SourceParameters
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

/-- Construct the literal earlier source record from the original context. -/
theorem source_parameter_setup
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) :
    ∃ s : EarlierA5Setup T L V (normalizer (L : Set G)) (normalizer (V : Set G)),
      zpowers s.z.val = V₁ ∧ s.v.val = markedV d.flag.flag.module := by
  obtain ⟨c, e, hv, _, ha⟩ := source_coordinates_with_quotient d
  have hC : centralizer (V₁ : Set G) = centralizer ({c.singular.val} : Set G) := by
    calc
      _ = centralizer (zpowers c.singular.val : Set G) :=
        congrArg (fun W : Subgroup G => centralizer (W : Set G)) c.line_eq.symm
      _ = _ := by rw [zpowers_eq_closure, centralizer_closure]
  have hmax := (Section03.A5Setup.normalizer_maximal_unique d.hypothesis d.chosen d.quotient).1
  have hu : maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) =
      {normalizer (L : Set G)} := by
    ext N
    constructor
    · intro hN
      exact Set.mem_singleton_iff.mpr (d.unique_maximal_overgroup N hN.1 hN.2)
    · intro hN
      rw [Set.mem_singleton_iff] at hN
      subst N
      exact ⟨hmax, sup_le L.le_normalizer d.normalizes_L⟩
  refine ⟨{
    local_component := d.hypothesis.local_component
    quotient := e
    uniform_A5 := fun _ => d.uniform_A5
    coordinates := c.coordinates
    normalizes := sup_le d.chosen.normalizes d.flag.T_normalizes
    actor_quotient := ha
    module_le := d.chosen.le_sylow
    local_normalizer := rfl
    module_normalizer := rfl
    normalizer_le := d.module_normalizer
    unique_overgroup := hu
    centralizer_eq := d.sylow_centralizer d.normalizes_L
    v := c.nonsingular
    z := c.singular
    nonsingular := c.form_nonsingular
    z_nonidentity := c.singular_ne_one
    singular := c.form_singular
    fusion := d.flag.normalizer_controls_fusion_of_nonsingular_centralizer hCv
    abelian_closure := ?_
    nonsingular_centralizer := by simpa only [hv] using hCv
    singular_escape := hC ▸ houtside }, c.line_eq, hv⟩
  exact SourceAbelian.source_closure_abelian d hA312 c.singular.val c.line_eq
    (show ¬ centralizer ({c.singular.val} : Set G) ≤ normalizer (L : Set G) from
      hC ▸ houtside) hcounter


/-- All source parameter conclusions of 13.6.25 now follow from the original
context, without a separate earlier-source setup record. -/
theorem source_13_6_25_of_context
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) :
    (∀ i : ℕ, i = 0 ∨ i = 1 →
      ChapterE.indexedWeakClosure V (T : Subgroup G) i ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter3.NormalIn (ChapterE.indexedWeakClosure V (T : Subgroup G) i)
        (L ⊔ (T : Subgroup G))) ∧
    (∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G),
      1 < ChapterE.generationParameter H) ∧
    (∀ H ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable H →
      H ≤ normalizer (L : Set G)) ∧
    ChapterE.globalR V = 3 ∧ 1 < ChapterE.globalW V (T : Subgroup G) := by
  obtain ⟨s, _, _⟩ := source_parameter_setup d hA312 hCv houtside hcounter
  exact source_13_6_25_knownSimple d.hypothesis.qtke s

/-- The first residual of 13.6.27 lies in the original line centralizer. -/
theorem source_initial_residual_of_context
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (V₁ : Set G) ∧
      1 < ChapterE.generationParameter H ∧
      (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H ∧
      ¬ (pResidual 2 H).map H.subtype ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  obtain ⟨s, hs, _⟩ := source_parameter_setup d hA312 hCv houtside hcounter
  have hc : centralizer ({s.z.val} : Set G) = centralizer (V₁ : Set G) := by
    rw [← hs, zpowers_eq_closure, centralizer_closure]
  have hT : (T : Subgroup G) ≤ centralizer ({s.z.val} : Set G) := by
    rw [hc]
    exact d.flag.one_invariant.trans
      (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  simpa only [hc] using exists_initial_residual_knownSimple d.hypothesis.qtke s hT

/-- The original large-prime core exclusion, on each actual H_z member. -/
theorem source_quotient_pCore_eq_bot_of_context
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) (h1338 : Earlier1338Two T)
    (L₁ G₁ : Subgroup G) {H : Subgroup G}
    (hH : H ∈ Section08.Source.Hz L₁ (T : Subgroup G) G₁ (normalizer (L : Set G)))
    (p : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    pCore p (H ⧸ pCore 2 H) = ⊥ := by
  obtain ⟨s, _, _⟩ := source_parameter_setup d hA312 hCv houtside hcounter
  exact quotient_pCore_eq_bot_of_original_setup s h1338 L₁ G₁ hH p hp hlarge

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
