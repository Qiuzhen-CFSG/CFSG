module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.TorusActions
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceBorel

/-!
# Assembly boundary for the native torus data

The normalized synchronized torus supplies the literal map, its full
Cartan range and its action on every native whole-root chart. The final
constructor assembles `SourceBorel.TorusData` directly whenever the charts
are the synchronized source charts. No torus-action premise remains.

Source: Fong--Seitz II (1974), (10.10)--(10.12), printed pp.223--224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open RootPresentationRecognition
open ReeF4.CentralCovers.OddPrimary.Order

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
  (d : SourcePositive.Charts Q split m)

def normalizedTorusData
    (ha : ∀ t i a,
      normalizedSynchronizedTorus Q split c t *
          SourceAngular.sourceRoot Q split d i a *
            (normalizedSynchronizedTorus Q split c t)⁻¹ =
        SourceAngular.sourceRoot Q split d i
          (SourceBorel.rootAction (fixedTorusEquiv m t) i a)) :
    SourceBorel.TorusData Q split d where
  h := normalizedSynchronizedTorus Q split c
  range_eq := normalizedSynchronizedTorus_range Q split c
  injective := by
    intro a b hab
    have hab' : synchronizedTorus Q split c
        ((torusCharacterEquiv (m := m)).symm a) =
        synchronizedTorus Q split c
          ((torusCharacterEquiv (m := m)).symm b) := by
      simpa only [normalizedSynchronizedTorus, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom] using hab
    have hst := synchronizedTorus_injective Q split c hab'
    exact (torusCharacterEquiv (m := m)).symm.injective hst
  action := ha

/-- The full native torus data for the actual synchronized source charts. -/
def synchronizedTorusData
    (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) = synchronizedPositivePoint Q split c i a) :
    SourceBorel.TorusData Q split d :=
  normalizedTorusData Q split c d (normalizedSynchronizedTorus_action Q split c d hd)

@[simp] theorem synchronizedTorusData_h
    (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) = synchronizedPositivePoint Q split c i a) :
    (synchronizedTorusData Q split c d hd).h = normalizedSynchronizedTorus Q split c := rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
