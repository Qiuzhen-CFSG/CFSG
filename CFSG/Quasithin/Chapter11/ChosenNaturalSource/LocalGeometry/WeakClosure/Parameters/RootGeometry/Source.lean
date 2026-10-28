module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.Linear
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.Symplectic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.G2
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Closure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.MinimalG2

/-!
# The natural A₂ calculations in the source weak closure

The inner-actor calculation is discharged for the literal full automizer
in all three markings and every coefficient degree, including nonsplit covers.
E.3.10 applies it to each weak-closure generator,
and the fixed-line identity then gives the centralization clause.
The numerical equality globalS=m remains with the owning natural-parameter
task; the preceding flag identity comes from the flag-Cartan owner. The final
assembly owner is qt-d-1222-natural-weak-closure-source.

Minimal fixed-space recognition is also proved in all three rows, retaining
only the earlier cubic and TI source clauses. Hyperplane centralizer control
remains with this parameter task; source 11.2.2 is not yet complete.
Source: Aschbacher--Smith 11.2.2(4), printed pp.767--768.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- All three source markings satisfy the A₂ inner-actor assertion on the
original module and Sylow group, with no numerical or splitting premise. -/
theorem natural_two_family (c : Coordinates D S.field) :
    letI := D.elementary
    ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) 2 →
      A ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  cases c with
  | sl3 m => exact RootActors.sl3_two_family D S m
  | sp4 m => exact RootActors.sp4_two_family D S m
  | g2 m => exact RootActors.g2_two_family D S m

/-- Source clause (4), with the entire local A₂ calculation discharged.
The numerical equality remains with this parameter owner and the earlier
fixed-line identity with qt-d-1222-natural-flag-cartan; the parent
qt-d-1222-natural-weak-closure-source retains their final assembly. -/
theorem natural_weakClosure_bound {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hs : @globalS G _ V D.elementary = naturalParameter D S c)
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    {j : ℕ} (hj : j < naturalParameter D S c - 1) :
    indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
      f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G) :=
  weakClosure_bound_of_two_family D S f (natural_two_family D S c) hs hline hj

/-- Source clause (4) in the SL₃ row, with its full-automizer A₂ calculation
proved and only the separately produced numerical and earlier flag inputs explicit. -/
theorem sl3_weakClosure_bound
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
    (hs : @globalS G _ V D.elementary = S.field.degree)
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    {j : ℕ} (hj : j < S.field.degree - 1) :
    indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
      f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G) :=
  weakClosure_bound_of_two_family D S f (RootActors.sl3_two_family D S m) hs hline hj

/-- Minimal fixed-space recognition and A₂ containment, on the same original
flag and full automizer. Only the preceding TI conclusion and the already
proved fixed-codimension family are explicit. -/
theorem rootGeometry_of_fixedCodimensions {c : Coordinates D S.field}
    (f : InvariantFlag c) (hmodel : FixedCodimensions D S c)
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) : RootGeometry D S f := by
  refine ⟨?_, natural_two_family D S c⟩
  intro U hUV hcor hres
  have hU : U ≠ ⊥ := by
    intro hz
    have hh := hmodel.dimension
    rw [← hz,hcor] at hh
    omega
  have hCN := (hypothesisE61_of_ti D S hti).localCentralizer_le_normalizer hU hUV
  cases c with
  | sl3 m =>
    exact Or.inr ⟨⟨m⟩, MinimalFixed.sl3_minimal_fixed D S m f hmodel hUV hcor hCN hres⟩
  | sp4 m =>
    obtain ⟨l,hl⟩ := MinimalFixed.sp4_minimal_fixed D S m f hUV hcor hCN hres
    exact Or.inl ⟨l,hl.le⟩
  | g2 m =>
    exact Or.inl (MinimalFixed.g2_minimal_fixed D S m f hUV hcor hCN hres)

/-- The complete root-geometry family, with all local calculations discharged.
The earlier cubic containment and TI facts belong to
qt-d-1222-natural-preliminary-source; the parent
qt-d-1222-natural-weak-closure-source retains their source assembly. -/
theorem natural_rootGeometry_of_cubic_source {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hcubic : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) : RootGeometry D S f :=
  rootGeometry_of_fixedCodimensions D S f
    (natural_fixedCodimensions_of_cubic_source D S c hcubic) hti

/-- Actual application of the complete root family to source clause (3).
The r lower bound remains with this parameter owner, via hyperplanes; the
three-space centralizer and the earlier TI/cubic facts retain their original
component and preliminary producers. -/
theorem natural_global_parameters_of_cubic_source {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hcubic : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hr : (naturalParameter D S c : ℕ∞) ≤ globalR V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    ((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c :=
  global_parameters D S f (natural_fixedCodimensions_of_cubic_source D S c hcubic)
    (natural_rootGeometry_of_cubic_source D S f hcubic hti)
    (hypothesisE61_of_ti D S hti) hr hthree

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
