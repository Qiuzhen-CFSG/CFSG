module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.PrimitiveRecognition.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.PrimitiveRecognition.Six
public import Theory.GroupAction.AbelianNormalComponents
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Component assembly for primitive alternating Sylow overgroups

The degree-six branch is solved by the existing solvable-parabolic
classification. An actual PSL₃(2) identification in degree seven makes
each component the whole overgroup, by simplicity and relative
subnormality. In degree eight a nontrivial abelian normal subgroup acts
transitively, is self-centralizing, and excludes components.

The final assembly below remains conditional on three independent
permutation-geometric inputs: the degree bound, the seven-point model,
and the abelian normal subgroup in degree eight. It does not claim the
unconditional primitive recognition theorem until these are proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.13,
printed p.74 (PDF p.85), final paragraph.
-/

public section
open Subgroup MulAction Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

private theorem component_eq_top_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (D : Subgroup G) (hD : IsComponent G D) : D = ⊤ := by
  let := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact (hD.1.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left
    ((Subgroup.nontrivial_iff_ne_bot D).mp inferInstance)

/-- An actual seven-point PSL₃(2) model identifies every component with
the same matrix quotient. No ambient normality of the component is assumed. -/
theorem alternating_primitive_seven_component_models_of_equiv
    (X : Subgroup (alternatingGroup (Fin 7)))
    (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (D : Subgroup X) (hD : IsComponent X D) : AlternatingSubgroupModels 7 D := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup X := e.isSimpleGroup
  exact Or.inr ⟨rfl, ⟨((MulEquiv.subgroupCongr
    (component_eq_top_of_simple D hD)).trans topEquiv).trans e⟩⟩

/-- The actual abelian normal subgroup in the eight-point overgroup suffices
to exclude components; a model of its quotient would not suffice. -/
theorem alternating_primitive_eight_not_isComponent_of_abelian_normal
    (X : Subgroup (alternatingGroup (Fin 8))) (hp : IsPreprimitive X (Fin 8))
    (A : Subgroup X) (hn : A.Normal) (ha : IsMulCommutative A) (hne : A ≠ ⊥)
    (D : Subgroup X) : ¬ IsComponent X D := by
  let := hp
  let := hn
  let := ha
  exact not_isComponent_of_abelian_normal_primitive (Ω := Fin 8) A hne D

/-- Conditional assembly of the three genuine permutation inputs. The
unconditional source recognition still requires their independent producers. -/
theorem alternating_primitive_component_recognition_of_geometry
    (hbound : AlternatingPrimitiveDegreeBound)
    (hseven : AlternatingPrimitiveSevenModel)
    (height : AlternatingPrimitiveEightAbelianNormal)
    (m : ℕ) (hm : 6 ≤ m) : AlternatingPrimitiveComponentRecognition m := by
  intro S X hS hX hp hthree hdouble D hD
  have hle := hbound m hm S X hS hX hp hthree hdouble
  have hcases : m = 6 ∨ m = 7 ∨ m = 8 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (alternating_six_proper_sylow_overgroup_not_isComponent S X hS hX D hD).elim
  · obtain ⟨e⟩ := hseven S X hS hX hp hthree hdouble
    exact alternating_primitive_seven_component_models_of_equiv X e D hD
  · obtain ⟨A, hn, ha, hne⟩ := height S X hS hX hp hthree hdouble
    exact (alternating_primitive_eight_not_isComponent_of_abelian_normal
      X hp A hn ha hne D hD).elim

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
