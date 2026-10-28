module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SymplecticFour
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentAutomizer

/-!
# The natural Sp4 exclusion for the actual component automizer

Apply the natural-action obstruction to the literal quotient N_H(L)/C_H(L).
Its original normalizer-Sylow image is Sylow and makes the component image a
normal supplement. Earlier B.6.8 supplies minimal parabolicity of this exact
quotient, so the natural Sp4 action over a field larger than two is impossible.

Source: Aschbacher--Smith B.6.9, printed p.116. Natural identification remains
an explicit earlier representation-recognition input; the automizer, Sylow,
and supplement are all constructed from the original component.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
open ChapterK.Symplectic
variable {G F V : Type*} [Group G] [Finite G]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- B.6.9's diagram obstruction in the actual component automizer. -/
theorem component_automizer_not_natural_symplectic_four
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) {L : Subgroup G}
    (hL : IsComponent G L) [IsSimpleGroup L] (heven : 2 ∣ Nat.card L)
    (ho : componentOrbit L (T : Subgroup G) = pResidual 2 G)
    (ρ : Representation (ZMod 2) (NormalizerAction.Star L) V)
    (hcard : 2 < Nat.card F) :
    ¬ Nonempty (NaturalIdentification (F := F)
      (ρ.comp (NormalizerAction.componentImage L).subtype)) := by
  rintro ⟨h⟩
  let : (NormalizerAction.componentImage L).Normal :=
    Subgroup.Normal.map inferInstance (NormalizerAction.quotient L)
      (QuotientGroup.mk'_surjective (NormalizerAction.C L))
  obtain ⟨S, hS, hmin⟩ := component_automizer_minimalParabolic T hP hL heven ho
  have hgen : NormalizerAction.componentImage L ⊔ (S : Subgroup _) = ⊤ := by
    rw [hS]
    exact component_automizer_sylow_supplement T hL ho
  exact not_minimalParabolic_of_natural_symplectic_four S
    (NormalizerAction.componentImage L) hgen ρ h hcard hmin

end CFSG.Quasithin.ChapterB
