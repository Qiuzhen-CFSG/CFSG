module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ActionFacts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ResidualAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.SourceReduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.SymplecticApplication

/-!
# The normalized component: Borel placement and symplectic identification

The actual A₅ marking gives Lᵥ = [Lᵥ,Tᵥ]. Perfect central descent connects
the book's outer group of K* to the faithful action on K. The marked
three-conjugate product proves that Lᵥ* centralizes a* but not z*.
Consequently a uniform centralizer calculation on the center of Tᵥ* ∩ K*
excludes the configuration in any subgroup containing Lᵥ*.

`source_symplectic_reduction` assembles the complete model placement and
root calculations, including exceptional covers and nonsplit extensions.
It constructs an actual Sp₄(2ᵐ) component-image equivalence and compatible
Sylow/Borel marking, retaining the source (i)/(ii) provenance. Only the
earlier local configuration and complete classification alternatives remain
inputs to this conditional reduction.

`false_of_normalized_component_and_multiplier` passes this output to the
separate SymplecticBorel argument through `SymplecticInputs`. The exact
I.1.3 universal-kernel theorem remains an explicit premise of that later
application; it is not needed for the component-image identification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.6, printed p.927.
-/
