module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CenterComparison.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Parabolic.Complete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Complete

/-!
# The original natural weak-closure source family

The proved parameter values and full G₂ weak-closure theorem discharge every
numerical and G₂ premise of the non-normalization argument. The actual F.7
critical pair then gives the outside-H obstruction, with the source SL₃
centralizer condition retained. The literal flag, relative residuals and
nonsplit central quotients remain unchanged.

The explicit earlier flag and component conclusions belong to the preceding
source producers and are discharged by qt-d-1222-natural-local-geometry.
The re-exported Generation.source_conclusion proves all alternatives of
11.2.1 using the completed odd-kernel normalizer theorem, actual automizer
bounds and doubled-module recognition. Its 11.3.6--7 applications discharge
the generation input while retaining their preceding shadow hypotheses.
The earlier conditional native-cover APIs remain re-exported.

Source: Aschbacher--Smith 11.2.1--2 and 11.2.4--5, printed pp.766--770.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))

include hunique hthree hline hcomponent in
/-- The original noncentral-closure hypothesis excludes the G₂ marking;
the remaining markings are compared through the same faithful automizer. -/
theorem not_g2_of_source_noncentral_zero
    (hW : ⁅V,Source.weakClosureZero (T : Subgroup G) V⁆ ≠ ⊥) :
    ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier))) := by
  rintro ⟨mg⟩
  have hmg := Parameters.localM_of_fixedCodimensions D S
    (Parameters.natural_fixedCodimensions D S (Coordinates.g2 mg))
  have hp := (Parameters.source_parameters D S f hunique hthree hline).1
  have hn := S.nonbinary
  cases c with
  | sl3 m => simp only [Parameters.naturalParameter] at hp hmg; omega
  | sp4 m => simp only [Parameters.naturalParameter] at hp hmg; omega
  | g2 m =>
    have hw := G2.CenterComparison.source_zero_centralizes D S m f hunique hthree hline hcomponent
    rw [←source_zero_eq_indexed] at hw
    exact hW (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hw.trans inf_le_right)))

include hunique hthree hline hcomponent in
/-- All three source 11.2.4 conclusions, with the parameter and G₂
weak-closure obligations discharged. Only the specified earlier flag and
component results remain explicit for the local-geometry assembly owner. -/
theorem source_nonnormalization
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V))
    (hW : ⁅V,Source.weakClosureZero (T : Subgroup G) V⁆ ≠ ⊥)
    (hSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
    (P : Sylow 2 (f.Li 1))
    (hfix : f.Vi 0 = f.Vi 1 ⊓ centralizer
      ((P : Subgroup (f.Li 1)).map (f.Li 1).subtype : Set G))
    (hradical : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (hmoveSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      ⁅V,f.Ri 1⁆ ≤ f.Vi 1) :
    Source.weakClosureZero (T : Subgroup G) V ≤ f.Ri 1 ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      globalR V ≤ (2*S.field.degree : ℕ) := by
  have hG2 := not_g2_of_source_noncentral_zero D S f hunique hthree hline hcomponent hW
  have he : Parameters.naturalParameter D S c=S.field.degree := by
    cases c with
    | sl3 m => rfl
    | sp4 m => rfl
    | g2 m => exact (hG2 ⟨m⟩).elim
  have hp := Parameters.source_parameters D S f hunique hthree hline
  rw [he] at hp
  have hfirst := (hp.2.2.2 0 (by have := S.nonbinary; omega)).2.trans inf_le_right
  rw [←source_zero_eq_indexed] at hfirst
  exact Nonnormalization.conclusions_of_earlier_source D S f hab hW hSL3 hp.2.2.1.1
    hcomponent P hfix hG2 hradical hp.2.2.1.2 hmoveSL3 hfirst

include hunique hthree hline hcomponent in
/-- Source 11.2.5 for the actual outside H. The F.7 pair is constructed,
and the full source non-normalization theorem supplies its contradiction. -/
theorem source_weakClosureObstruction
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G))
    (hSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
    (P : Sylow 2 (f.Li 1))
    (hfix : f.Vi 0 = f.Vi 1 ⊓ centralizer
      ((P : Subgroup (f.Li 1)).map (f.Li 1).subtype : Set G))
    (hradical : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (hmoveSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      ⁅V,f.Ri 1⁆ ≤ f.Vi 1) :
    Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) H := by
  apply obstruction_of_nonnormalization D S H hTH hout f hSL3
  intro hSL hab hW
  exact (source_nonnormalization D S f hunique hthree hline hcomponent
    hab hW hSL P hfix hradical hmoveSL3).2.1
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure

