module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Recognition.SL3
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Recognition.Sp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Generation

/-!
# Small-action exclusion and the remaining parabolic source input

The two actual natural markings now give reciprocal field-line recognition
and the first alignment in 11.2.4. The original abelian conjugate span excludes
all such small symmetric actions, uniformly over the original conjugates in T.
This supplies the root input to all three source conclusions and to the
constructed critical-pair obstruction. The explicit SL3 condition is retained.

The remaining local inputs are the first three ParabolicCalculations. The
centralizer-generation clause is now proved from those earlier clauses; the
original record argument is retained for compatibility. Its construction is an unproved
obligation of qt-d-1222-natural-conjugate-nonnormalization, not a genuine source
hypothesis. The parent qt-d-1222-natural-weak-closure-source discharges the
permitted preceding numerical, G2, flag and relative-component statements.
These consumers do not yet establish the whole source theorem.

Source: Aschbacher--Smith, 11.2.4--5, printed pp.769--770.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Both surviving natural rows recognize the literal reciprocal field line. -/
theorem smallRootRecognition {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))) :
    SmallRootRecognition f := by
  cases c with
  | sl3 m => exact sl3_smallRootRecognition m f
  | sp4 m => exact Recognition.sp4_smallRootRecognition m f
  | g2 m => exact (hG2 ⟨m⟩).elim

/-- The first alignment in 11.2.4, now from the two actual small-action coranks. -/
theorem small_alignment {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (W : Subgroup G) (hs : SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W)
    (hn : W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Alignment (f.Vi 0) V g :=
  alignment_of_small_commutator_line f hG2 g hs
    (smallRootRecognition f hG2 g hg hne W hs hn)

/-- Uniform small-action exclusion with the original abelian-span hypothesis. -/
theorem noSmallActions {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V))
    (hr : (S.field.degree : ℕ∞) < globalR V) : NoSmallActions f := by
  intro g hg hne
  exact no_smallAction_of_alignment f hab hr g hne (small_alignment f hG2 g hg hne)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Source 11.2.4 with reciprocal-root recognition and normalized-plane alignment
proved. The remaining local obligation is the actual offender/parabolic calculation. -/
theorem conclusions_of_calculations {c : Coordinates D S.field} (f : InvariantFlag c)
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
    (hcalculations : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      RootParabolic.ParabolicCalculations f (V.map (MulAut.conj g).toMonoidHom)) :
    Source.weakClosureZero (T : Subgroup G) V ≤ f.Ri 1 ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      globalR V ≤ (2 * S.field.degree : ℕ) := by
  apply conclusions_of_root_and_parabolic D S f hab hW hSL3 hparameters hK P hfix hG2
  · exact RootParabolic.small_alignment f hG2
  · intro g hg hne hs
    exact RootParabolic.parabolic_of_three_calculations f hG2 g hg hne hs
      (hcalculations g hg hne).outside (hcalculations g hg hne).proper
      (hcalculations g hg hne).fixed

/-- Application to the actual constructed critical pair, with the same remaining local inputs. -/
theorem obstruction_of_calculations {c : Coordinates D S.field} (f : InvariantFlag c)
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
    (hcalculations : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      RootParabolic.ParabolicCalculations f (V.map (MulAut.conj g).toMonoidHom)) :
    Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) H := by
  apply obstruction_of_nonnormalization D S H hTH hout f hSL3
  intro hSL3' hab hW
  exact (conclusions_of_calculations D S f hab hW hSL3' hparameters hK P hfix
    hG2 hcalculations).2.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization
