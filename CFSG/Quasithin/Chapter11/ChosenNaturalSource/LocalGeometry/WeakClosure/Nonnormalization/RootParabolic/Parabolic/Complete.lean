module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Parabolic.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Parabolic.Outside

/-!
# All local calculations for source 11.2.4 and its critical-pair consumer

The outside-radical calculation completes the parabolic argument. Combined
with reciprocal root recognition, proper-displacement exclusion, full-cover
plane saturation and point fusion, it proves all three 11.2.4 conclusions.
The second theorem supplies the non-normalization implication to the actual
critical pair constructed for 11.2.5, preserving the explicit SL₃ condition.
No local action, root, commutator, or alignment callback remains.

As allowed by this task's contract, the preceding source results are explicit:
11.2.2's numerical bounds and first-line fixation belong to
qt-d-1222-natural-weak-parameters; its G₂ clause belongs to
qt-d-1222-natural-g2-weak-closure; component uniqueness belongs to
qt-d-1222-natural-relative-components; the Sylow fixed-space and radical
action identities belong to qt-d-1222-natural-flag-cartan. The final source
owner qt-d-1222-natural-weak-closure-source discharges these earlier premises.
These exports are the complete conditional 11.2.4 argument, not an assertion
that the preceding source results have already been assembled.

Source: Aschbacher--Smith, 11.2.4--5, printed pp.769--770.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- All three conclusions of 11.2.4, with only the authorized earlier source results explicit. -/
theorem conclusions_of_earlier_source {c : Coordinates D S.field} (f : InvariantFlag c)
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V))
    (hW : ⁅V, Source.weakClosureZero (T : Subgroup G) V⁆ ≠ ⊥)
    (hSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
    (hparameters : (S.field.degree : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (hK : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (P : Sylow 2 (f.Li 1))
    (hfix : f.Vi 0 = f.Vi 1 ⊓ centralizer ((P : Subgroup (f.Li 1)).map
      (f.Li 1).subtype : Set G))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hradical : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (hs : @globalS G _ V D.elementary = S.field.degree)
    (hmoveSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      ⁅V,f.Ri 1⁆ ≤ f.Vi 1)
    (hfirst : f.Vi 0 ≤ centralizer
      (Source.weakClosureZero (T : Subgroup G) V : Set G)) :
    Source.weakClosureZero (T : Subgroup G) V ≤ f.Ri 1 ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      globalR V ≤ (2 * S.field.degree : ℕ) := by
  apply conclusions_of_outside_calculation D S f hab hW hSL3 hparameters hK P hfix
    hG2 hradical hs hmoveSL3
  intro g hg _ houtside
  let := D.elementary
  have hA : V.map (MulAut.conj g).toMonoidHom ≤ Source.weakClosureZero (T : Subgroup G) V :=
    le_sSup ⟨g,rfl,hg⟩
  exact RootParabolic.Outside.small_action_of_outside_radical f hG2 hs g hg
    (hfirst.trans (Subgroup.centralizer_le hA)) houtside

/-- The actual constructed critical-pair application, with all local 11.2.4 calculations discharged. -/
theorem obstruction_of_earlier_source {c : Coordinates D S.field} (f : InvariantFlag c)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G))
    (hSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
    (hparameters : (S.field.degree : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (hK : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (P : Sylow 2 (f.Li 1))
    (hfix : f.Vi 0 = f.Vi 1 ⊓ centralizer ((P : Subgroup (f.Li 1)).map
      (f.Li 1).subtype : Set G))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hradical : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (hs : @globalS G _ V D.elementary = S.field.degree)
    (hmoveSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      ⁅V,f.Ri 1⁆ ≤ f.Vi 1)
    (hfirst : f.Vi 0 ≤ centralizer
      (Source.weakClosureZero (T : Subgroup G) V : Set G)) :
    Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) H := by
  apply obstruction_of_nonnormalization D S H hTH hout f hSL3
  intro hSL3' hab hW
  exact (conclusions_of_earlier_source D S f hab hW hSL3' hparameters hK P hfix
    hG2 hradical hs hmoveSL3 hfirst).2.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization
