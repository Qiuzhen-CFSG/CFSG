module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.Generation
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.ModelAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcluded

/-!
# Conditional assembly of the odd-centralizer branch

The escaping Cartan actor cannot centralize W: otherwise the 4.4 normalizer
theorem puts its full normalizer in M. Its literal fixed space therefore has
the nondegeneracy and codimension supplied by the doubled-action calculation.
The established singular-space argument gives r≥n+2, while the attained
Cartan generation argument gives n(H)=2. These feed the original chosen-orbit
terminal theorem when the independent weak-closure proof supplies w>2.

The final wrappers discharge both finite action inputs on the original chosen
orbit. Odd-normalizer control, escaping actors, nonsingular centralizers, and
the weak-closure bound remain explicit earlier-source inputs.
Source: Aschbacher--Smith, 12.1.9--11, printed pp.793--794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

/-- The actual escaping odd actor supplies the literal fixed space, rather
than an arbitrary subspace of the right dimension. -/
theorem doubledOrbit_oddFixedSpaces_of_many_of_source_inputs
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hodd : OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)))
    (hactors : EscapingOddActors (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    letI := D.doubledOrbit_elementary h
    B.OddActionGeometry → B.OddFixedSpaces := by
  let := D.doubledOrbit_elementary h
  intro hgeometry U hUW hescape
  obtain ⟨X, hX, ho, hXM, hXU, hXN⟩ := hactors U hUW hescape
  have hn : ¬ X ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G) :=
    fun hc => hXN (hodd X hX ho hXM hc)
  obtain ⟨hQ, hcodim⟩ := hgeometry X ho hXM hn
  exact ⟨X, ho, hXM, hn, hXU, hQ, hcodim⟩

/-- Both numerical outputs of 12.1.9, on the original chosen orbit and
every original H*. All remaining producer obligations are explicit. -/
theorem doubledOrbit_parameters_of_many_of_source_inputs
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (1 : ℕ∞) < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T)
    (hodd : OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)))
    (hactors : EscapingOddActors (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)))
    (haction : LargePrimeSylowAction (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) T) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers → B.OddActionGeometry →
      B.OddFixedSpaces ∧ ((n + 2 : ℕ) : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      ∀ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
        ChapterE.generationParameter H = 2 := by
  let := D.doubledOrbit_elementary h
  intro hcentral hgeometry
  have hf := D.doubledOrbit_oddFixedSpaces_of_many_of_source_inputs h hmany B hodd hactors hgeometry
  exact ⟨hf, B.globalR_ge_add_two (D.doubledOrbit_normalizer_eq h B.orbit_eq) hcentral hf,
    fun _ hH => D.doubledOrbit_generation_eq_two_of_many h hmany B hw hodd haction hH hcentral⟩

/-- Actual application to the retained terminal assembly. The weak-closure
owner supplies w>2; the three source producers must discharge the other inputs. -/
theorem doubleNatural_excluded_of_many_of_odd_source_inputs
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (2 : ℕ∞) < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T)
    (hodd : OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)))
    (hactors : EscapingOddActors (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)))
    (haction : LargePrimeSylowAction (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) T) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers → B.OddActionGeometry → False := by
  let := D.doubledOrbit_elementary h
  intro hcentral hgeometry
  obtain ⟨_, hr, hgen⟩ := D.doubledOrbit_parameters_of_many_of_source_inputs h hmany B
    (lt_trans (by decide) hw) hodd hactors haction hcentral hgeometry
  exact doubleNatural_excluded_of_many_of_parameters h D hmany B hw hr hgen

/-- The fixed-space action calculation on the original chosen orbit. -/
theorem doubledOrbit_oddActionGeometry_of_many
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    B.OddActionGeometry := by
  let := D.doubledOrbit_elementary h
  exact B.oddActionGeometry

include D in
/-- The large-prime calculation uses the actual ambient Sylow in its
component normalizer; no torus invariance premise is required. -/
theorem doubledOrbit_largePrimeSylowAction_of_many
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    LargePrimeSylowAction (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) T :=
  B.largePrimeSylowAction D.sylow_normalizes_component

/-- Both numerical outputs, with the two finite action inputs discharged.
The independent odd-normalizer, escaping-actor and centralizer producers feed
this consumer; the classification assembly retains their final discharge. -/
theorem doubledOrbit_parameters_of_many_of_odd_inputs
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (1 : ℕ∞) < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T)
    (hodd : OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)))
    (hactors : EscapingOddActors (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers →
      B.OddFixedSpaces ∧ ((n + 2 : ℕ) : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      ∀ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
        ChapterE.generationParameter H = 2 := by
  let := D.doubledOrbit_elementary h
  intro hcentral
  exact D.doubledOrbit_parameters_of_many_of_source_inputs h hmany B hw hodd hactors
    (D.doubledOrbit_largePrimeSylowAction_of_many hmany B) hcentral
    (D.doubledOrbit_oddActionGeometry_of_many h hmany B)

/-- Literal classification consumer with both finite action facts proved.
The parent odd-centralizer and weak-closure assemblies retain the remaining
source inputs, rather than assuming either action conclusion. -/
theorem doubleNatural_excluded_of_many_of_odd_inputs
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (2 : ℕ∞) < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T)
    (hodd : OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)))
    (hactors : EscapingOddActors (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers → False := by
  let := D.doubledOrbit_elementary h
  intro hcentral
  exact D.doubleNatural_excluded_of_many_of_odd_source_inputs h hmany B hw hodd hactors
    (D.doubledOrbit_largePrimeSylowAction_of_many hmany B) hcentral
    (D.doubledOrbit_oddActionGeometry_of_many h hmany B)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
