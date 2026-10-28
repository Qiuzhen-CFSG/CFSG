module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Binary.Parabolic
public import Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry.ParabolicRoot

/-!
# The binary component's literal matrix root action

The actual V-action has order two and is induced by full Sp₄(2) conjugation
on Sp₄(2)′. It fixes the transported maximal parabolic pointwise. The intrinsic
parabolic calculation supplies coordinates in which this image is a matrix
root action. Composing those coordinates with the component equivalence proves
the source root assertion, retaining Sp₄(2)′ as the carrier acted on.

Source: Aschbacher–Smith, E.6.8(2b), printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- In the maximal-parabolic case the actual induced V-action is a literal
matrix root action on the derived symplectic carrier. -/
theorem binary_parabolic_root_action (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) (hp : MaximalParabolic L (L ⊓ M)) :
    SymplecticRootAction L V 1 := by
  obtain ⟨e, hcard, hnat, P, hP, ⟨S, hSP⟩, hfix⟩ :=
    binary_parabolic_image_data h earlier hU hL hm hp
  obtain ⟨f, r, hroot⟩ := parabolic_action_is_root _ hcard hnat P hP S hSP hfix
  refine ⟨component_normalized_by_V h hU hL,
    ZMod 2, inferInstance, inferInstance, by simp, e.trans f, r, ?_⟩
  have he : (MulAut.congr (e.trans f)).toMonoidHom =
      (MulAut.congr f).toMonoidHom.comp (MulAut.congr e).toMonoidHom := by
    ext a x
    rfl
  rw [he, ← map_map]
  exact hroot

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
