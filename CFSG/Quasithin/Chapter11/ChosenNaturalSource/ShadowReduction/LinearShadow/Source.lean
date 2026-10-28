module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FFAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Source

/-!
# Proposition 11.3.2 after the parameter/component reduction

`Preceding1132` contains only the particular conclusions of §§11.0--11.2
used in the shadow argument. The original flag is arbitrary, so the same
interface can be used for the later swapped-I application. The numerical
11.3.4 argument derives the SL₃/Sp₄ alternative, excludes every G₂ marking
of the same quotient, and identifies the original global parameter with n.
The actual residual-component output then supplies the inputs of 11.3.7;
the assembled common-core and compatible-Cartan contradiction proves all
four clauses of `Proposition1132At` on the original chosen quotient.

The rank-one entry point also applies the doubled-module exclusion to prove
k=n, retaining the literal residual O²(H) and relative normality. The final
entry point applies the complete parameter/model sieve, but explicitly
retains its universal normalized 7.0.1 input and odd-kernel control. These
are not hidden in `Preceding1132`. The normalized source must apply to every
selected overcomponent and chosen module, not just the initial D.

The unresolved parameter/component source discharge belongs to
qt-d-1222-shadow-parameter-component. The §§11.0--11.2 conclusions and
odd-kernel control retain qt-d-1222-natural-local-geometry and its producers.
Final discharge stays with qt-d-1222-shadow-linear-geometry and its parent
qt-d-1222-natural-shadow-reduction. Thus these conditional entry points do
not claim the source theorem with only the preceding chapter clauses.

Source: Aschbacher--Smith, refs/quasithin.pdf, 11.0.4, 11.2.1--5 and
11.3.2--9, printed pp.759--775. The common-core assembly preserves the
field-four cover obstruction, odd-degree reduction and corrected sections
V₂ and P/V₂.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Selected preceding-source clauses: 11.0.4, 11.2.1, the parameter and
weak-closure conclusions of 11.2.2, and the earlier `Preceding1133` clauses.
There is no shadow classification, common core or compatible field premise. -/
structure Preceding1132 (c : Coordinates D S.field) (f : InvariantFlag c)
    (H : Subgroup G) : Prop where
  preceding : Preceding1133 D S (c.binarySubspace (f.space 0)) H
  generation : WeakClosure.Generation.Conclusion D S H
  global_s : @ChapterE.globalS G _ V D.elementary =
    WeakClosure.Parameters.naturalParameter D S c
  parameters : (WeakClosure.Parameters.naturalParameter D S c : ℕ∞) < ChapterE.globalR V ∨
    (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
      ChapterE.globalR V = WeakClosure.Parameters.naturalParameter D S c ∧
      ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
  weak : D.centralQuotientPreimage (c.binarySubspace (f.space 0)) ≤
    centralizer (Source.weakClosureZero (T : Subgroup G) V : Set G)
  prime_residual : ∀ p : ℕ, p.Prime →
    ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
      (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
        p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
    primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G))
  cubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
    Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L

private theorem not_g2_of_classical_marking
    (hm : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))) :
    ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) := by
  rintro ⟨mg⟩
  have hg := WeakClosure.Parameters.localM_eq_naturalParameter D S (.g2 mg)
  simp only [WeakClosure.Parameters.naturalParameter] at hg
  have hn := S.field.degree_pos
  rcases hm with hm | hm
  · obtain ⟨m⟩ := hm
    have hd := WeakClosure.Parameters.localM_eq_naturalParameter D S (.sl3 m)
    simp only [WeakClosure.Parameters.naturalParameter] at hd
    omega
  · obtain ⟨m⟩ := hm
    have hd := WeakClosure.Parameters.localM_eq_naturalParameter D S (.sp4 m)
    simp only [WeakClosure.Parameters.naturalParameter] at hd
    omega

/-- Derive the 11.3.4 numerical/model reductions and supply the actual
parameter-component result to the common-core construction. -/
theorem Preceding1132.toPreceding1137
    {c : Coordinates D S.field} {f : InvariantFlag c}
    (p : Preceding1132 c f H)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (hc : ¬ Proposition1132At D S (c.binarySubspace (f.space 0)) H)
    (r : ParameterComponent.Conclusion S H) : CommonCore.Preceding1137 c f H := by
  obtain ⟨hm,hs,_⟩ := ParameterComponent.source_marking_and_parameter
    s p.preceding hc c p.global_s p.generation
  have he : WeakClosure.Parameters.naturalParameter D S c = S.field.degree :=
    ENat.natCast_inj.mp (p.global_s.symm.trans hs)
  have halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) := by
    rcases hm with hm | hm
    · obtain ⟨m⟩ := hm
      exact .inl ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩
    · obtain ⟨m⟩ := hm
      exact .inr ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩
  refine ⟨p.preceding,not_g2_of_classical_marking hm,r.component,r.model,hs,halt,
    ?_,p.weak,p.prime_residual,p.cubic⟩
  rcases p.parameters with hr | ⟨⟨m⟩,hr,hcent⟩
  · exact .inl (he ▸ hr)
  · exact .inr ⟨⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨m.groupEquiv⟩⟩,he ▸ hr,hcent⟩

/-- The full four-clause target from preceding geometry and the actual
outside residual-component result, with all subsequent premises discharged. -/
theorem proposition1132_of_parameter_component
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H) (r : ParameterComponent.Conclusion S H) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H := by
  classical
  by_contra hc
  exact hc (proposition1132_of_preceding1137 c f hu s (p.toPreceding1137 s hc r))

/-- The doubled-module argument proves k=n and the actual residual component
from 11.3.5, before applying the full common-core and Cartan contradiction. -/
theorem proposition1132_of_rankOneReduction
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H) (r : ParameterComponent.RankOneReduction S H) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H := by
  classical
  by_contra hc
  have hs := (ParameterComponent.source_marking_and_parameter
    s p.preceding hc c p.global_s p.generation).2.1
  have hK := ParameterComponent.Doubled.source_parameter_component s p.preceding hc
    f rfl r p.generation hs.symm.le
  exact hc (proposition1132_of_parameter_component c f hu s p hK)

/-- Original-quotient application of the full model sieve and Cartan
contradiction. Universal normalized 7.0.1 and odd-kernel control remain explicit
source inputs; no 11.3 conclusion or terminal local callback is assumed. -/
theorem proposition1132_of_normalized_source
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (h701 : ∀ (J W : Subgroup G) (E : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter7.NormalizedSource.Alternatives G E.orbitRepresentation E.orbitComponent) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H := by
  classical
  by_contra hc
  have r := ParameterComponent.conclusion_of_normalized_source s p.preceding hc
    f rfl p.global_s hcontrol h701 p.prime_residual p.cubic
  exact hc (proposition1132_of_parameter_component c f hu s p r)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
