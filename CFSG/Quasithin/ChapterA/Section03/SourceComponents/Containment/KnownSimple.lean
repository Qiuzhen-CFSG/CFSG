module
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Containment
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Full-catalogue unique component containment

The proved simultaneous Theorems A and C supply the radical-quotient and
simple-model inputs in the source containment argument. Thus the first
assertion of A.3.12 holds for the full known-simple catalogue without any
additional classification premise. This assertion is distinct from its
proper-embedding list.

Source: Aschbacher–Smith A.3.12, printed pp.47–48; its application in
1.2.4 and 2.5.6, printed pp.505 and 554.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A local component for the full Sylow lies in exactly one ambient C-component. -/
theorem containment_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents T) :
    ∃! L : Subgroup G, L.IsCComponent ∧ B ≤ L := by
  apply containment (fun X _ _ => Section02.theoremA_knownSimple (G := X))
    (source_model_inputs_of_theoremC (fun X _ _ => Section02.theoremC_knownSimple (G := X)))
    hG hO T B hB

end CFSG.Quasithin.ChapterA.Section03.SourceComponents
