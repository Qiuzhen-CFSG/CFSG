module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Reselection

/-!
# The actual A₆ exclusion consumer in source 14.3.4

Hypothesis1331 records the literal four source assumptions, using the
canonical faithful family and actual excluded carriers. The original
Counterexample supplies it. The proved arbitrary-component reselection
then makes full Theorem13.8.1 applicable to each original faithful actor
whose central quotient is A₆. The original Sp₆(2)/U₄(3) exclusions give
contradiction, retaining the original quotient and central-cover maps.

Theorem1381 is an explicit universal earlier source implication, not a
proved classifier. Its producer is qt-13-08. Full 14.3.4(1–2) additionally
requires the genuine 13.3.2 classification and normality/maximality, from
qt-13-03-preliminaries, and the U₃(3) exclusion13.3.16 from qt-13-03.
The repository's current Section13.1/13.3/13.8 aggregators explicitly do
not establish those source assemblies. Accordingly this file proves the
applicability and central-quotient exclusion stage only; it does not wrap
or assert EarlierFaithfulClassification as a new assumption or theorem.

Source: Aschbacher–Smith, Hypothesis13.3.1 and 13.3.2(5), pp.884–885;
Theorem13.8.1, p.946; Lemma14.3.4(1–2), p.990.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The four numbered clauses of Hypothesis 13.3.1, without the additional
Sp₆(2) and U₄(3) exclusions imposed later in 14.3.1(1). -/
structure Hypothesis1331 (T : Sylow 2 G) (L : Subgroup G) : Prop where
  qtke : IsSimpleQTKE KnownSimple.IsKnownSimple G
  local_component : L ∈ MainForward.faithfulLocalComponents T
  no_larger_field : ¬ LargerEvenFieldModel G
  no_linear : ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL G n 2
  no_alternating_nine : ¬ Nonempty (G ≃* alternatingGroup (Fin 9))
  no_sporadic : ∀ s : KnownSimple.SporadicName,
    s = .m22 ∨ s = .m23 ∨ s = .m24 ∨ s = .he ∨ s = .j4 →
      ¬ Nonempty (G ≃* s.Carrier)
  five_minimal : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ K ∈ MainForward.faithfulLocalComponents T,
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))

/-- The original source counterexample retains every clause of 13.3.1. -/
theorem hypothesis1331 {T : Sylow 2 G} {L : Subgroup G} (d : Counterexample T L) :
    Hypothesis1331 T L :=
  ⟨d.qtke, d.local_component, d.no_larger_field, d.no_linear,
    d.no_alternating_nine, d.no_sporadic, d.five_minimal⟩

/-- The complete universal source 13.8.1 recognition implication. This is an
explicit earlier theorem parameter; its producer is qt-13-08. -/
def Theorem1381 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X),
    Hypothesis1331 S A →
      Nonempty ((A ⧸ centralCore A) ≃* alternatingGroup (Fin 6)) →
      ClassicalGroup.IsPSp X 3 2 ∨ ClassicalGroup.IsPSU X 4 3

/-- Apply the genuine earlier recognition theorem to an arbitrary original
faithful component, using the proved reselection rather than a new FSU premise. -/
theorem not_A6_centralQuotient_of_source
    {T : Sylow 2 G} {L : Subgroup G} (d : Counterexample T L)
    (source1381 : Theorem1381.{u}) (C : Subgroup G)
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C) :
    ¬ Nonempty ((C ⧸ centralCore C) ≃* alternatingGroup (Fin 6)) := by
  intro hsix
  have dC : Counterexample T C := reselect_A6 d hC hf hsix
  rcases source1381 G T C (hypothesis1331 dC) hsix with hsp | hsu
  · exact d.no_symplectic_six hsp
  · exact d.no_unitary_four hsu

/-- The ordinary A₆ alternative of 13.5.2 is excluded using its actual
center-free core quotient, without confusing it with the triple-cover branch. -/
theorem not_A6_coreQuotient_of_source
    {T : Sylow 2 G} {L : Subgroup G} (d : Counterexample T L)
    (source1381 : Theorem1381.{u}) (C : Subgroup G)
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6)) :=
  fun hsix => not_A6_centralQuotient_of_source d source1381 C hC hf
    (A6_centralQuotient_of_coreQuotient C hsix)

/-- The same consumer excludes a supplied actual central cover of A₆ on
C/O₂(C). The kernel comparison is literal; no abstract cover tag is used. -/
theorem not_central_cover_A6_of_source
    {T : Sylow 2 G} {L : Subgroup G} (d : Counterexample T L)
    (source1381 : Theorem1381.{u}) (C : Subgroup G)
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C)
    (f : (C ⧸ pCore 2 C) →* alternatingGroup (Fin 6))
    (hsurj : Function.Surjective f) (hk : f.ker = center (C ⧸ pCore 2 C)) : False :=
  not_A6_centralQuotient_of_source d source1381 C hC hf
    ⟨centralQuotient_equiv_of_cover C f hsurj hk⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
