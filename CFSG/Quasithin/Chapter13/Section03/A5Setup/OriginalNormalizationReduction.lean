module

public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic

/-!
# The A₅ normalization reduction at every Sylow subgroup

The uniform A₅ clause of Hypothesis 13.3.1 is independent of the chosen
Sylow subgroup. Conjugation carries the canonical local family and its
intrinsic module to the original Sylow subgroup; it also identifies the
literal quotients by the two-cores. Thus every faithful component at every
Sylow subgroup has A₅ quotient in this branch.

The proved original maximality theorem consequently supplies Hypothesis
12.2.1 for every actor appearing in the universal 13.3.2 normalization
input of the Chapter 13.6 source consumers. Only the A₅ case of the original
Chapter 10 normalization theorem is needed for this input; no general
13.1.7 reduction or chosen-module premise is required.

Source: Aschbacher–Smith, Hypothesis 13.3.1(4) and 13.3.2, pp.884–885,
using Sylow conjugacy and the original normalization theorem 10.0.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalNormalizationReduction
open Chapter1.Section02.Adequate ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
include h e

/-- In the uniform A₅ branch, the literal two-core quotient of every faithful
local component is A₅, including components at other Sylow subgroups. -/
theorem five_quotient_of_faithful (S : Sylow 2 G) (I : Subgroup G)
    (hI : I ∈ MainForward.faithfulLocalComponents S) :
    Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  let a : G ≃* G := MulAut.conj g
  have hST : (S : Subgroup G).map a.toMonoidHom = (T : Subgroup G) := by
    change (g • S : Sylow 2 G).toSubgroup = T.toSubgroup
    rw [hg]
  let J := I.map a.toMonoidHom
  have hi := (mem_faithfulLocalComponents_iff S I).mp hI
  have hJ : J ∈ Chapter1.L G (T : Subgroup G) := by
    rw [← hST]
    exact (Chapter1.mem_L_map_iff a.toMonoidHom a.injective).mpr hi.1
  have hfJ : J ∈ MainForward.faithfulLocalComponents T := by
    apply (mem_faithfulLocalComponents_iff_module T (h.qtke.evenCharacteristic T)).mpr
    refine ⟨hJ, ?_⟩
    rw [intrinsicSignalizerModule_map_of_injective a.toMonoidHom a.injective I]
    exact fun hz => hi.2.2 ((map_eq_bot_iff_of_injective _ a.injective).mp hz)
  obtain ⟨eJ⟩ := h.five_minimal ⟨e⟩ J hfJ
  let b : I ≃* J := I.equivMapOfInjective a.toMonoidHom a.injective
  exact ⟨(QuotientGroup.congr (pCore 2 I) (pCore 2 J) b (pCore_map_iso 2 b)).trans eJ⟩

/-- The uniform Chapter 13.3.2 normalization callback used by the original
13.6 consumers follows from the A₅ case of the original Chapter 10 input. -/
theorem normalization_of_A5_source
    (h10 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple S I →
      Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)) →
      (S : Subgroup G) ≤ normalizer (I : Set G)) :
    ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
      (S : Subgroup G) ≤ normalizer (I : Set G) := by
  intro S I hI
  obtain ⟨eI⟩ := five_quotient_of_faithful h e S I hI.local_component
  exact h10 S I (OriginalMaximality.hypothesis1221 hI eI) ⟨eI⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalNormalizationReduction
