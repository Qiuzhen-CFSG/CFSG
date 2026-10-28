module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.Assembly
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.Native
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.Residual

/-!
# The ambient M₁₂ heart extension

The native heart action extends faithfully to the actual full automorphism
group, using checked ten-coordinate matrices for its degree-24 carrier.
The scalar-centralizer calculation identifies the given ambient action with
conjugation on its solvable residual, preserving both supplied markings.
This constructs the complete `AmbientExtension` witness with no extra premise.

For every such witness, the inner-automorphism preimage is exactly the solvable
residual, and every element of odd prime order lies in that residual.
Source: Aschbacher–Smith H.11.1, printed pp.392–393 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations

/-- The faithful ambient extension with the specified residual and module markings. -/
noncomputable def ambientExtension {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ) : AmbientExtension ρ h :=
  Ambient.extensionOfRepresentation h Ambient.automorphismRepresentation
    Ambient.automorphismRepresentation_faithful Ambient.automorphismRepresentation_inner

/-- The witness required by the H.11 module calculations always exists. -/
theorem nonempty_ambientExtension {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ) :
    Nonempty (AmbientExtension ρ h) := ⟨ambientExtension ρ h⟩

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
