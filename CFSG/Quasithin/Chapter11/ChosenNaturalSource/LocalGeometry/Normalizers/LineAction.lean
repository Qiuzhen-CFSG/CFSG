module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.Section

/-!
# The two line-action branches of source 11.2.3

The preceding flag identities identify the Cartan-stable line, its rank-one
residual and its centralizing radical. The actual line action then supplies
cyclicity and normality for the zero-fixed-space Frattini argument. In the
other branch, the source component orbit bound makes the residual normal in
the line normalizer, and the exact core-quotient action identifies its kernel's
Sylow subgroup with the original radical.

The scalar-line marking and the independent Sylow-normalizer theorem remain
explicit. The source assembly owner must discharge them, as well as the
preceding flag identities and radical-normalizer alternative. Neither final
containment nor decomposition is assumed here.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.2.3, printed pp.768--769.
-/

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original two-clause consumer, with the positive component and section
Sylow assertions and the zero-branch normality now discharged. The flag
identities belong to the preceding flag/Cartan producer. The scalar-line
geometry and source Sylow-normalizer theorem still require their own proofs. -/
theorem chosen_source_11_2_3_of_line_geometry
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hfixR : f.Ri 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hscalar : V ⊓ centralizer (L : Set G) = ⊥ →
      IsCyclic (lineImage f X) ∧ LinearGroup.IsRegularOnNonzero (lineImage f X) ∧
        lineImage f T ≤ normalizer (lineImage f X : Set _))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) := by
  have hXU := chosen_cartan_normalizes_line_of_fixedSpace f hX hfixed
  apply chosen_source_11_2_3_of_action_steps D S f hX hXU hNT _ _ hradical
  · intro hz
    obtain ⟨hcyc, hreg, hTN⟩ := hscalar hz
    exact chosen_line_normalized_of_singer f hX hXU hcyc hreg hTN
  · intro _ hC
    exact chosen_line_positive_steps_of_flag_geometry S f hm hfix hfixR hC

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
