module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.SetupCoordinates
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.NativeComplete
public import CFSG.Quasithin.Chapter13.Section02.A5Local.Fusion

/-!
# The original A₅ terminal argument with its source coordinates assembled

The constructed source flag supplies the actual normalizer action, singular
line, nonsingular point and invariant three-space. The nonsingular point
centralizer bound separates the two nonzero module orbits and consequently
gives full fusion control. These facts instantiate the proved F.9 construction
and native strict quadratic bound on the literal quotient U_H/V₁.

Only the original earlier A.3.12 theorem, the genuine 13.6.7(1) nonsingular
centralizer bound, the singular centralizer escape, the counterexample, and
the exceptional component conclusion remain. In particular no independent
coordinate, fusion, F.9 or B.4 witness is required. This does not assert that
the earlier 13.6.7 component argument has been assembled.

Source: Aschbacher–Smith 13.2.6, 13.6.2, 13.6.7 and the final paragraph of
13.6, printed pp.879,926,928,935.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- Apply the terminal contradiction at the original source flag and its literal line centralizer. -/
theorem terminal_contradiction_of_A5_context
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (hcomponents : Components.Conclusion
      ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G)))) : False := by
  let := d.elementary
  obtain ⟨c, hv, _⟩ := source_coordinates d
  have hC : centralizer (V₁ : Set G) = centralizer ({c.singular.val} : Set G) := by
    calc
      _ = centralizer (zpowers c.singular.val : Set G) :=
        congrArg (fun W : Subgroup G => centralizer (W : Set G)) c.line_eq.symm
      _ = _ := by rw [zpowers_eq_closure, centralizer_closure]
  exact terminal_contradiction_of_marked_A5_native d hA312 c.coordinates
    c.nonsingular c.singular c.form_nonsingular c.singular_ne_one c.line_eq
    c.form_singular c.alternating_le
    (d.flag.normalizer_controls_fusion_of_nonsingular_centralizer hCv)
    (by simpa only [hv] using hCv) c.third_mark
    (hC ▸ houtside) hcounter (hC ▸ hcomponents)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
