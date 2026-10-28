module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Complete
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Source
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.RadicalStar
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal.NormalizerControl
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal.EscapingGeneration.Source

/-!+# The local contradiction in source 13.1.7

The original canonical radicals are starred. Supplement uniqueness and
Thompson movement therefore feed the complete module and centralizer sieve,
giving TI for the literal normalizer-moved module. The Frattini supplement
controls the normalizer of its Sylow centralizer. The escaping E₂-generated
overgroup then contradicts the terminal containment theorem.

Only the earlier quasisimple classification and rigidity clauses of 13.1.2
are retained here. Their pointwise Chapter12 assembly is separate; no local
star, orbit, FF, supplement, TI, normalizer or escaping witness is assumed.
Source: Aschbacher--Smith, 13.1.4--14, printed pp.867--876.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter12.Section02 Supplements
open SourceCentralizerStructure.Elimination
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Supply the exact canonical-star premise in both the supplement and
escaping-subgroup branches from the original radical exclusion. -/
theorem canonicalStars (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Escape.CanonicalStars T := by
  intro L hL hn p hp ho hd
  let : Fact p.Prime := ⟨hp⟩
  exact (show Context T L p from ⟨h,hmany,hL,hn,ho,hd⟩).radical_star

/-- Assemble every local branch of 13.1.7 at the actual maximal faithful
nonquasisimple member. Only the two earlier 13.1.2 clauses remain. -/
theorem false_of_maximal_nonquasisimple (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrig : Escape.QuasisimpleRigidity T) (hclass : Escape.QuasisimpleClassification T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) : False := by
  have hs := canonicalStars h hmany
  obtain ⟨hsupp,hmove⟩ := source_lemma_13_1_9 h hmany hs hrig hclass hL hn
  have hf : L ∈ nonquasisimpleFaithful T :=
    ⟨(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mpr
      ⟨hL.1.1,hL.2⟩,hn⟩
  obtain ⟨K,hK,hLK,_,_,_,_,_,p,hp,ho,_,hd,_⟩ :=
    h.maximal_counterexample_of_many hmany hf
  have he : K = L := hL.1.2 K hK.1 hLK
  subst K
  let : Fact p.Prime := ⟨hp⟩
  let c : Context T L p := ⟨h,hmany,hL,hn,ho,hd⟩
  have hTI := (c.ti_of_radical_star hmove c.radical_star).1
  have hu := Terminal.normalizerMoved_centralizer_normalizer_unique h hL hn
    (fun B hB hrad => hsupp B ⟨hB,hrad⟩)
  exact Terminal.false_of_source_escaping h hmany hs hrig hclass hL hn hTI hu

/-- Original 13.1.7 for the whole faithful family, in the actual
multiple-overgroup branch and conditional only on earlier 13.1.2. -/
theorem nonquasisimpleFaithful_eq_empty_of_quasisimple_sources
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrig : Escape.QuasisimpleRigidity T) (hclass : Escape.QuasisimpleClassification T) :
    nonquasisimpleFaithful T = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro L hL
  obtain ⟨K,_,_,hf,hn,_⟩ := h.maximal_counterexample_of_many hmany hL
  exact false_of_maximal_nonquasisimple h hmany hrig hclass hf hn.2

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
