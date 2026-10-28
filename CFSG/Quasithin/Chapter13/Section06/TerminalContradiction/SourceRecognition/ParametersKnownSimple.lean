module
public import CFSG.Quasithin.Chapter13.Section06.SourceAbelian.KnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ParameterSetup

/-!
# Original A₅ parameters without an embedding callback

The callback-free closure theorem constructs the literal earlier source
record from the marked context. Its quotient actor, singular line and
nonsingular point are unchanged. The remaining point-centralizer bound and
counterexample assumptions are the original source hypotheses.

Source: Aschbacher–Smith 13.6.2 and 13.6.25, printed pp.926,934.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source SourceParameters
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

/-- Construct the literal earlier source record from the original context. -/
theorem source_parameter_setup_knownSimple
    (d : Context T L V V₁ V₂ V₃)
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
  exact SourceAbelian.source_closure_abelian_knownSimple d c.singular.val c.line_eq
    (show ¬ centralizer ({c.singular.val} : Set G) ≤ normalizer (L : Set G) from
      hC ▸ houtside) hcounter



end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
