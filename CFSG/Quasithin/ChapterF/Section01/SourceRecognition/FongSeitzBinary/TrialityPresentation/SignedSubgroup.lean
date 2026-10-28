module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.PositiveSubgroup
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.WeylAction

/-!
# Signed root generation in the literal triality source quotient

For the actual quotient `X / Q.D`, an explicit pair of simple-root conjugation
actions reduces generation by all six positive and six negative root groups to
the positive subgroup and the two marked rank-one Weyl words. The scalar maps
are transported through the compatible original cubic/fixed-field marking;
the negative parameters therefore retain their original source values.

This is a conditional source application: constructing the negative source
maps and verifying the action equations remains part of source recognition.
It does not identify the quotient with a triality model.

Source: GLS3 2.3.5 and 2.4.8(e); DGS Theorem D, printed p.224.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation

variable {X F : Type*} [Group X] [Field F] {Psrc : Fin 2 → Subgroup X}
variable {Q : MarkedQuotient Psrc} {split : SplitData Q.tits}
variable {m : ℕ} {hm : 0 < m} {σ : F ≃+* F}

/-- Source data for the negative root groups and their finite simple-root
conjugation actions. The positive maps and equations come from the preceding
map-free collector contract. -/
structure SignedRootData (d : PositiveRootData Q split m hm σ) where
  negativeShort : Fin 3 → Multiplicative F →* X ⧸ Q.D
  negativeLong : Fin 3 →
    Multiplicative (ScalarMarking.SourceFixed (σ := σ)) →* X ⧸ Q.D
  actions :
    (SignedRoots.mk (n := m) (hn := hm) d.roots
      (fun i => (negativeShort i).comp
        d.scalars.extension.symm.toRingHom.toAddMonoidHom.toMultiplicative)
      (fun i => (negativeLong i).comp
        d.scalars.fixed.symm.toRingHom.toAddMonoidHom.toMultiplicative)).ActionRelations

namespace SignedRootData
variable (d : PositiveRootData Q split m hm σ) (s : SignedRootData d)

/-- The complete signed maps on the model coordinates, transported from the
literal original fields by the already specified scalar marking. -/
def roots : SignedRoots (n := m) (hn := hm) (X ⧸ Q.D) where
  positive := d.roots
  negativeShort := fun i => (s.negativeShort i).comp
    d.scalars.extension.symm.toRingHom.toAddMonoidHom.toMultiplicative
  negativeLong := fun i => (s.negativeLong i).comp
    d.scalars.fixed.symm.toRingHom.toAddMonoidHom.toMultiplicative

/-- Their generated subgroup is exactly the positive source `U` together with
the two simple-root words. -/
theorem signedClosure_eq_sourceUnipotent_sup_simpleWords :
    s.roots.signedClosure = split.U ⊔
      Subgroup.closure {s.roots.nA 1, s.roots.nB 1} := by
  rw [SignedRoots.signedClosure_eq_simpleClosure s.roots s.actions]
  exact congrArg (fun H : Subgroup (X ⧸ Q.D) =>
    H ⊔ Subgroup.closure {s.roots.nA 1, s.roots.nB 1}) d.positive

end SignedRootData
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
