module

public import Theory.Alternating.Theorem523Reduction
public import Theory.GroupTheory.CoveringPGroupDescent
/-!
# Reduced quasisimple covers of A₈

Schur's universal double cover has two-group kernel. Every quasisimple
cover of A₈ has kernel of order dividing two, so a cover with trivial
two-core is injective. The result concerns the given epimorphism.

Source: GLS III, Theorem 5.2.3, applied in Aschbacher--Smith, Section 12.6,
printed p.822. The existing Schur presentation and universality proof are
reused without enumerating the alternating group.
-/

public section

open Subgroup Theory.GroupTheory
open GLS3.Chapter5.SchurPresentation
namespace AlternatingEight
variable {E : Type*} [Group E] [Finite E] [IsQuasisimple E]
theorem reduced_cover_injective (f : E →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f) (hcore : pCore 2 E = ⊥) : Function.Injective f := by
  have hp : IsPGroup 2 (schurAlternatingCovering 3).toMonoidHom.ker :=
    IsPGroup.of_card (n := 1) (by rw [natCard_ker_schurAlternatingCovering]; decide)
  exact (theorem_5_2_3_b_universality 3 (by decide) (by decide)).injective_of_pGroup_kernel
    hp (show Covering E (alternatingGroup (Fin 8)) from ⟨f, hf⟩) hcore
end AlternatingEight
