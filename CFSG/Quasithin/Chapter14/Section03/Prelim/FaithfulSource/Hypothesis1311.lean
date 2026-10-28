module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource
public import CFSG.Quasithin.Chapter13.Section01.SourceHypotheses

/-!
# The original 13.3.1 hypotheses imply 13.1.1

Section 13.3 excludes all Lie types over larger binary fields, whereas
Section 13.1 excludes the rank-two families. Every constructor of the
complete rank-two family lies in the larger-field family when f > 1;
the small derived cases have f = 1 and hence cannot occur. All named
sporadic exclusions transport definitionally through the actual catalogue.

This connects the same original faithful component and Sylow subgroup to
the source 13.1 reductions. No quotient classification is assumed or proved.
Source: Aschbacher--Smith, Hypotheses 13.1.1 and 13.3.1, pp.865 and 884.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section01
universe u
variable {G : Type u} [Group G]

/-- The complete rank-two family embeds in the later larger-field exclusion. -/
theorem largerEvenFieldModel_of_rankTwo {f : ℕ} (hf : 1 < f)
    (h : ClassificationModels.IsRankTwoModel G f) : LargerEvenFieldModel G := by
  refine ⟨f, hf, ?_⟩
  cases h with
  | linear _ h => exact Or.inl ⟨3, Or.inl h⟩
  | unitary_four _ h => exact Or.inl ⟨4, Or.inr (Or.inl h)⟩
  | unitary_five _ h => exact Or.inl ⟨5, Or.inr (Or.inl h)⟩
  | symplectic _ h => exact Or.inl ⟨2, Or.inr (Or.inr (Or.inl h))⟩
  | g2 _ h => exact Or.inr (Or.inl h)
  | triality _ h => exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  | ree_f4 m _ he h => exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, he, Or.inr h⟩)))))))
  | symplectic_derived he _ => omega
  | g2_derived he _ => omega
  | tits he _ => omega

variable [Finite G]

/-- Retain the same ambient group and Sylow subgroup when applying §13.1
inside the later Hypothesis13.3.1 source configuration. -/
theorem Hypothesis1331.hypothesis1311 {T : Sylow 2 G} {L : Subgroup G}
    (h : Hypothesis1331 T L) : Hypothesis1311 T :=
  { simpleQTKE := h.qtke
    no_rankTwo := fun _ hf he => h.no_larger_field (largerEvenFieldModel_of_rankTwo hf he)
    no_linear := h.no_linear
    no_A9 := h.no_alternating_nine
    no_M22 := h.no_sporadic .m22 (by simp)
    no_M23 := h.no_sporadic .m23 (by simp)
    no_M24 := h.no_sporadic .m24 (by simp)
    no_He := h.no_sporadic .he (by simp)
    no_J4 := h.no_sporadic .j4 (by simp) }

/-- The original Chapter14 source counterexample supplies the exact earlier
13.1.1 hypotheses, without changing its selected faithful component. -/
theorem Counterexample.hypothesis1311 {T : Sylow 2 G} {L : Subgroup G}
    (d : Counterexample T L) : Hypothesis1311 T :=
  (hypothesis1331 d).hypothesis1311

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
