module

public import Theory.SpecificGroups.Tits.R1Presentation
public import Theory.GroupTheory.PresentedGroupBounds
public import Theory.SpecificGroups.Tits.R1WordCertificate.Relators
public import Theory.SpecificGroups.Tits.R1WordCertificate.Checked
public import Theory.SpecificGroups.Tits.R1WordCertificate.Shape

/-!
# A kernel-certified 1024-coset cover of the local R₁ presentation

The six-rule coset-word trace proves 304877 deductions using actual equations in
`ParrottR1Group`. Its 63938 acyclic definitions realize representatives, and its
1024 survivors supply all 18432 signed generator transitions. Every deduction is
checked by ordinary kernel reduction in bounded chunks. Every selected final
fact is additionally checked for its source, letter and destination.

The literal relators are proved equal to those of `R1Presentation`. The generic
soundness and cover-extraction theorems then give the cover without a finiteness
assumption. The untrusted producer, original artifacts and deterministic Lean
generator are preserved in
`refs/original/n-group-global/parrott-r1-word-certificate/`.

This is the cover of the local nine-generator presentation by the subgroup
`⟨r1,s1⟩`. The separate 1755-coset cover of the full presentation by `R₁` remains
in `R1AmbientCosetCover` and is not used here.

Source: Parrott (1972), §5, p. 683;
`refs/original/n-group-global/parrott-tits-presentation.md`.
-/

namespace Tits

open Subgroup.CosetWordCertificate R1WordCertificate

/-- The certified 1024-representative cover of Parrott's local R₁ presentation. -/
public def parrottR1CosetCover :
    Subgroup.GeneratorCosetCover parrottR1DihedralSubgroup
      parrottR1Generator (Fin 1024) := by
  have hall := all_hold valid
  have hinit : definitions.repr parrottR1Generator (survivor (0 : Fin 1024)) = 1 := by
    have hs : survivor (0 : Fin 1024) = 0 := by decide +kernel
    rw [hs]
    exact definitions.repr_zero _
  exact coverOfFacts facts survivor 0 hinit dest output hshape
    (by intro i a; exact hall (output i a) (hlt i a))

end Tits
