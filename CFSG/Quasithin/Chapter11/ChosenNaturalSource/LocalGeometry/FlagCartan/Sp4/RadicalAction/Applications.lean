module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.RadicalAction.Identities
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Orbits.Points
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Parabolic.Source

/-!
# The marked symplectic radical in the source nonnormalization consumer

The actual flag, its Sylow fixed point and the entire-cover radical identities
discharge the geometric premises in the existing 11.2.4 consumer.
The independent component input remains with qt-d-1222-natural-relative-components,
the numerical inputs with qt-d-1222-natural-weak-parameters, and the outside
calculation with qt-d-1222-natural-conjugate-nonnormalization. The final owner
qt-d-1222-natural-weak-closure-source discharges those premises and the preceding
source conditions; this is a conditional consumer, not the full source theorem.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction
open WeakClosure.Nonnormalization
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- The original source consumer with its marked-flag and radical inputs proved. -/
theorem source_conclusions_of_outside_calculation
    (hab : IsMulCommutative
      (Source.conjugateSpan (normalizer ((flag m S).Vi 0 : Set G)) V))
    (hW : ⁅V, Source.weakClosureZero (T : Subgroup G) V⁆ ≠ ⊥)
    (hSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      centralizer ((flag m S).Vi 1 : Set G) ≤ normalizer (L : Set G))
    (hparameters : (S.field.degree : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = S.field.degree ∧
        ¬ centralizer ((flag m S).Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (hK : Source.UniqueNoncentralComponent (normalizer ((flag m S).Vi 1 : Set G))
      ((flag m S).Vi 1) ((flag m S).Li 1))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hs : @globalS G _ V D.elementary = S.field.degree)
    (houtside : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ (flag m S).Ri 1 →
      SmallSymmetricAction (flag m S) (V.map (MulAut.conj g).toMonoidHom) ((flag m S).Vi 1)) :
    Source.weakClosureZero (T : Subgroup G) V ≤ (flag m S).Ri 1 ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      globalR V ≤ (2 * S.field.degree : ℕ) :=
  conclusions_of_outside_calculation D S (flag m S) hab hW hSL3 hparameters hK
    (Orbits.planeSylow S m) (Orbits.planeSylow_fixed S m) hG2
    (radical_centralizes_plane S m) hs (fun _ => commutator_le_plane S m) houtside

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction
