module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Parabolic.Fixed

/-!
# Source consumers of the actual fixed-plane calculation

The original centralizer identity now follows from the full displacement
plane and the earlier flag fact that R₂ centralizes V₂. Combined with the
proved centralizer-generation argument, it removes the last two local
callbacks from source 11.2.4 and from the constructed critical-pair consumer.
The explicit SL₃ centralizer condition and the whole nonsplit cover remain.

The outside-radical and proper-displacement branches are still local
obligations of qt-d-1222-natural-conjugate-nonnormalization. These conditional
consumers do not establish the entire source theorem. The preceding radical
centralization is owned by qt-d-1222-natural-flag-cartan; the named final owner
qt-d-1222-natural-weak-closure-source discharges it together with the earlier
numerical, component, G₂ and Sylow fixed-space inputs.

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

/-- Fixed-plane identification and centralizer generation are proved here.
The outside-radical and proper-displacement calculations remain with this
source assembly owner; this is still a conditional source reduction. -/
theorem conclusions_of_two_calculations {c : Coordinates D S.field} (f : InvariantFlag c)
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
    (houtside : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) (f.Vi 1))
    (hproper : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ (V ⊓ centralizer (L : Set G)) ≠ f.Vi 1 →
      ∃ l ∈ f.Li 1, SmallSymmetricAction f
        ((V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj l).toMonoidHom) V) :
    Source.weakClosureZero (T : Subgroup G) V ≤ f.Ri 1 ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      globalR V ≤ (2 * S.field.degree : ℕ) := by
  apply conclusions_of_root_and_parabolic D S f hab hW hSL3 hparameters hK P hfix hG2
  · exact RootParabolic.small_alignment f hG2
  · intro g hg hne hs
    exact RootParabolic.parabolic_of_two_calculations f hG2 hradical g hg hne hs
      (houtside g hg hne) (hproper g hg hne)

/-- Application to the actual constructed critical pair, with the same remaining local inputs. -/
theorem obstruction_of_two_calculations {c : Coordinates D S.field} (f : InvariantFlag c)
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
    (houtside : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) (f.Vi 1))
    (hproper : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ (V ⊓ centralizer (L : Set G)) ≠ f.Vi 1 →
      ∃ l ∈ f.Li 1, SmallSymmetricAction f
        ((V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj l).toMonoidHom) V) :
    Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) H := by
  apply obstruction_of_nonnormalization D S H hTH hout f hSL3
  intro hSL3' hab hW
  exact (conclusions_of_two_calculations D S f hab hW hSL3' hparameters hK P hfix
    hG2 hradical houtside hproper).2.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization
