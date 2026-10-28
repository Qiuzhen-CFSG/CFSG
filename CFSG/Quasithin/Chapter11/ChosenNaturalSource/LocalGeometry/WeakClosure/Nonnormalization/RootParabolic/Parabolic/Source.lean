module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Parabolic.Proper

/-!
# Source consumers with proper displacement excluded

The common-field-line argument discharges the proper-displacement branch
in both natural rows. Together with the fixed-plane and centralizer-span
calculations, it leaves only the outside-radical calculation in 11.2.4.
The literal original quotient and the explicit SL3 centralizer condition
remain in both the source conclusions and the actual critical-pair consumer.

These are still conditional reductions, not the complete source theorem.
The outside calculation stays with qt-d-1222-natural-conjugate-nonnormalization.
The exact earlier radical action belongs to qt-d-1222-natural-flag-cartan,
and the earlier numerical input belongs to qt-d-1222-natural-weak-parameters.
The final owner qt-d-1222-natural-weak-closure-source discharges these earlier
premises together with the G2, component and Sylow fixed-space inputs.

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

/-- All three source conclusions with only the outside-radical local calculation remaining. -/
theorem conclusions_of_outside_calculation {c : Coordinates D S.field} (f : InvariantFlag c)
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
    (houtside : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) (f.Vi 1)) :
    Source.weakClosureZero (T : Subgroup G) V ≤ f.Ri 1 ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      globalR V ≤ (2 * S.field.degree : ℕ) := by
  apply conclusions_of_root_and_parabolic D S f hab hW hSL3 hparameters hK P hfix hG2
  · exact RootParabolic.small_alignment f hG2
  · intro g hg hne hsmall
    exact RootParabolic.parabolic_of_outside_calculation f hab hG2 hs
      (strict_globalR_of_sl3_condition D S f hSL3 hparameters) hradical hmoveSL3
      g hg hne hsmall (houtside g hg hne)

/-- The constructed critical-pair obstruction with the proper-displacement premise discharged. -/
theorem obstruction_of_outside_calculation {c : Coordinates D S.field} (f : InvariantFlag c)
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
    (houtside : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) (f.Vi 1)) :
    Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) H := by
  apply obstruction_of_nonnormalization D S H hTH hout f hSL3
  intro hSL3' hab hW
  exact (conclusions_of_outside_calculation D S f hab hW hSL3' hparameters hK P hfix
    hG2 hradical hs hmoveSL3 houtside).2.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization
