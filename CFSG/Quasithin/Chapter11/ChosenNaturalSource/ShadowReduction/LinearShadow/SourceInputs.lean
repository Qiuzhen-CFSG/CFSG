module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Source
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesComplete

/-!
# Source branches and the remaining independent inputs to 11.3.2

The G₂ branch follows from the preceding generation and weak-closure
parameters alone: the same full automizer would have parameters n and 2n.
For the symplectic branch and for fields other than four, the proved
odd-normalizer analysis discharges odd-kernel control. Consequently, after
normalized 7.0.1, a remaining counterexample has the original SL₃(4) marking,
trivial fixed space and an original module of order 64. The cubic center of
the full quotient is retained.

The final application constructs normalized 7.0.1 at every selected chosen
module from the proved source 3.2.5 and the precise doubled and Mathieu
source exits. It constructs odd-kernel control from the uniform native J₄
cover, and then applies the original common-core, compatible-field and
Cartan contradiction. All flags and quotient maps remain those of D;
the argument also applies to a later swapped-I choice.

This does not discharge the independent doubled and Mathieu exits or the
native cover. Their producers are qt-d-1222-nonff-doubled,
qt-d-1222-nonff-mathieu and qt-model-j4-elementary-normalizer-cover, with
odd-normalizer assembly retained by qt-d-1222-natural-odd-kernel-normalizer.
The preceding geometry retains qt-d-1222-natural-local-geometry. Final
11.3.2 discharge remains with qt-d-1222-shadow-linear-geometry and its parent
qt-d-1222-natural-shadow-reduction.

Source: Aschbacher--Smith, refs/quasithin.pdf, 11.3.2--9, printed
pp.770--775, using 11.2.1--2, 7.0.1 and 4.4.3. The field-four cover
obstruction and the two distinct residual conventions remain in the
common-core construction; no compatible-field premise is added here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
open WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The G₂ branch of all four source clauses uses only the preceding
11.2.1--2 parameters, without component recognition or odd-kernel control. -/
theorem proposition1132_of_g2
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H := by
  classical
  by_contra hc
  have hs := (ParameterComponent.source_marking_and_parameter
    s p.preceding hc c p.global_s p.generation).2.1
  have he : WeakClosure.Parameters.naturalParameter D S c = S.field.degree :=
    ENat.natCast_inj.mp (p.global_s.symm.trans hs)
  have hm := WeakClosure.Parameters.localM_eq_naturalParameter D S c
  have hg := WeakClosure.Parameters.localM_eq_naturalParameter D S (.g2 m)
  rw [he] at hm
  simp only [WeakClosure.Parameters.naturalParameter] at hg
  have hn := S.field.degree_pos
  omega

section Normalized
variable (h701 : ∀ (J W : Subgroup G) (E : ChosenModule T J W),
    Hypothesis1223 KnownSimple.IsKnownSimple T J →
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    Chapter7.NormalizedSource.Alternatives G E.orbitRepresentation E.orbitComponent)

include h701 in
/-- All symplectic source cases discharge odd-kernel control, including q=4.
The normalized source theorem is required for the selected overcomponent. -/
theorem proposition1132_of_sp4_of_normalized_source
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H :=
  proposition1132_of_normalized_source c f hu s p
    (oddKernelNormalizer_of_sp4 D S m.groupEquiv) h701

include h701 in
/-- For every source field other than four, the odd-normalizer theorem
removes the extra kernel-control input from the complete shadow argument. -/
theorem proposition1132_of_field_ne_four_of_normalized_source
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H) (hn : S.field.degree ≠ 2) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H :=
  proposition1132_of_normalized_source c f hu s p
    (oddKernelNormalizer_of_field_ne_four D S hn) h701

include h701 in
/-- Under normalized 7.0.1, the only remaining source counterexample has
the full SL₃(4) action, its cubic quotient center and |V|=64. No central
quotient is silently replaced by its projective image. -/
theorem linear_four_of_counterexample_of_normalized_source
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (hc : ¬ Proposition1132At D S (c.binarySubspace (f.space 0)) H) :
    S.field.degree = 2 ∧
      Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64 := by
  classical
  have hnot : ¬ WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V) := by
    intro hcontrol
    exact hc (proposition1132_of_normalized_source c f hu s p hcontrol h701)
  have hm : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) := by
    cases S.natural with
    | sl3 m => exact m
    | sp4 m =>
      obtain ⟨m⟩ := m
      exact (hc (proposition1132_of_sp4_of_normalized_source h701 c f hu s p m)).elim
    | g2 m =>
      obtain ⟨m⟩ := m
      exact (hc (proposition1132_of_g2 c f s p m)).elim
  unfold WeakClosure.Generation.OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨r,hr,ho,A,hA,hAe,hAC,_,hout⟩ := hnot
  obtain ⟨hn,_,hz,hfixed,hcard⟩ := outside_linear_field_four D S hr ho A hA hAe hAC hout
  exact ⟨hn,hm,hz,hfixed,hcard⟩

end Normalized

/-- Original-quotient application with normalized 7.0.1 and odd-kernel
control constructed from their exact independent source inputs. The two
source exits quantify over every selected chosen module at the same G,T.
The native J₄ cover is a concrete model input, not an ambient J₄ conclusion. -/
theorem proposition1132_of_source_exits_and_elementary_cover
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    (hdoubled : ∀ (J W : Subgroup G) (E : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      E.MarkedDoubled → ¬ IsFFModule E.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : ∀ (J W : Subgroup G) (E : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      W = E.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses E.orbitRepresentation E.orbitComponent →
      Chapter7.NormalizedSource.HasMathieuCentralQuotient E.orbitComponent →
      ¬ IsFFModule E.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model)) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H := by
  have h701 (J W : Subgroup G) (E : ChosenModule T J W)
      (hJ : Hypothesis1223 KnownSimple.IsKnownSimple T J)
      (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
      Chapter7.NormalizedSource.Alternatives G E.orbitRepresentation E.orbitComponent :=
    E.sourceOrbit_alternatives_of_source_inputs_of_many hJ hmany
      (E.source325_of_many hJ hmany)
      (hdoubled J W E hJ hmany) (hmathieu J W E hJ hmany)
  by_cases hn : S.field.degree = 2
  · cases S.natural with
    | sl3 _ =>
      exact proposition1132_of_normalized_source c f hu s p
        (oddKernelNormalizer_of_elementary_cover D S C eC hcover) h701
    | sp4 m =>
      obtain ⟨m⟩ := m
      exact proposition1132_of_sp4_of_normalized_source h701 c f hu s p m
    | g2 m =>
      obtain ⟨m⟩ := m
      exact proposition1132_of_g2 c f s p m
  · exact proposition1132_of_field_ne_four_of_normalized_source h701 c f hu s p hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
