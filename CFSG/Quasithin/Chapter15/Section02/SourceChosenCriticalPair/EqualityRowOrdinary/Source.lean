module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.Selection
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.TerminalSource

/-!
# The direct ordinary escaping-overgroup contradiction

The original residual input selects an actual ordinary component whenever
the minimal escaping overgroup has F*(I) ≠ O₂(I). The even-model reduction
produces its genuine terminal model/action, whose original marked centralizer
is excluded by the direct residual argument. Thus the entire ordinary branch
is discharged without the partner residual identity or a uniqueness packet.

Source: Aschbacher--Smith 15.2.24 and the proof of 15.2.15,
printed pp.1117--1118, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 OrdinaryComponents
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

/-- A minimal escaping overgroup cannot have an ordinary component. All
component, model and marked-action witnesses are constructed internally. -/
theorem ResidualInput.ordinary_minimal_escape_false
    (r : ResidualInput h H B)
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* Wreath))
    (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (hF : generalizedFitting I ≠ pCore 2 I) : False := by
  obtain ⟨P,z,hP,hz,hzne,⟨c⟩⟩ := r.exists_component_data_direct hI hF
  exact r.ordinary_terminal_false c hquotient hI.1 hP hz hzne
    (r.ordinary_terminal_model c hquotient hI hP hz hzne)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
