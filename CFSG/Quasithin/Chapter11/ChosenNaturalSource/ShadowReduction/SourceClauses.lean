module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalInput
public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# The precise source clauses for the shadow reduction

Hypothesis1131At is the selected-witness form of Hypothesis 11.3.1: H is
an actual outside minimal local subgroup, it moves Ω₁Z(T), and in the
SL₃ case the centralizer of the actual quotient-line preimage lies in M.
Here M is the original N_G(L). The preceding geometric owner still has
to identify the supplied quotient subspace as the source T-invariant line.
Proposition1132At records all four requested conclusions as a target,
not as available hypotheses or an established theorem.

The proved application below transfers the nonabelian closure in 11.2.5
from N_G(V₁) to C_G(V₁), using the normalizer decomposition of 11.2.3.
This is the step giving clause (4) during 11.3.3. The fixed-space and
classification clauses of 11.3.2 remain separate obligations.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.2.3, 11.2.5 and 11.3.1--3, printed pp.768--771.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction

variable {G : Type*} [Group G]

/-- Agreement with the actual zero-th weak closure from E.3.13. -/
theorem weakClosureZero_eq_indexed (T V : Subgroup G) :
    Source.weakClosureZero T V = ChapterE.indexedWeakClosure V T 0 := by
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  unfold Source.weakClosureZero
  congr 1
  ext A
  exact (ChapterE.mem_gamma_zero_iff V T A).symm

private theorem conjugateSpan_eq_conjugateSpanBy (H V : Subgroup G) :
    Source.conjugateSpan H V = conjugateSpanBy V H :=
  (conjugateSpanBy_eq_iSup_conj V H).symm

variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V)

/-- The exact additional hypotheses of 11.3.1, with its moving H selected.
The chapter setup and the source line are supplied separately. -/
structure Hypothesis1131At (S : D.NonbinaryNaturalInput)
    (U₁ : Submodule (ZMod 2) D.chosenCentralQuotient) (H : Subgroup G) : Prop where
  outside : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))
  moves_omega_center :
    ⁅omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype), H⁆ ≠ ⊥
  linear_centralizer : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
    centralizer (D.centralQuotientPreimage U₁ : Set G) ≤ normalizer (L : Set G)

/-- All four conclusions of Proposition 11.3.2, as an unproved target.
Neither classification nor fixed-space vanishing is part of Hypothesis1131At. -/
structure Proposition1132At (S : D.NonbinaryNaturalInput)
    (U₁ : Submodule (ZMod 2) D.chosenCentralQuotient) (H : Subgroup G) : Prop where
  symplectic : Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree)
  centralizer_outside :
    ¬ centralizer (D.centralQuotientPreimage U₁ : Set G) ≤ normalizer (L : Set G)
  fixed_trivial : V ⊓ centralizer (L : Set G) = ⊥
  closure_nonabelian : Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2 →
    ¬ IsMulCommutative
      (Source.conjugateSpan (centralizer (D.centralQuotientPreimage U₁ : Set G)) V)

omit [Finite G] in
/-- The clause-(4) step of 11.3.3 on the original chosen quotient-line
preimage, from the literal 11.2.3 and 11.2.5 conclusions. -/
theorem nonabelian_centralizer_span_of_weakClosure
    (U₁ : Submodule (ZMod 2) D.chosenCentralQuotient) (H : Subgroup G)
    (hweak : Source.WeakClosureObstruction (T : Subgroup G) V
      (D.centralQuotientPreimage U₁) H)
    (hcore : Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2)
    (hsplit : normalizer (D.centralQuotientPreimage U₁ : Set G) =
      centralizer (D.centralQuotientPreimage U₁ : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (D.centralQuotientPreimage U₁ : Set G)))
    (hseed : normalizer (L : Set G) ⊓ normalizer (D.centralQuotientPreimage U₁ : Set G) ≤
      normalizer (V : Set G)) :
    ¬ IsMulCommutative
      (Source.conjugateSpan (centralizer (D.centralQuotientPreimage U₁ : Set G)) V) := by
  have hn := hweak.resolve_left (not_not.mpr hcore)
  change ¬ IsMulCommutative
    (Source.conjugateSpan (normalizer (D.centralQuotientPreimage U₁ : Set G)) V) at hn
  have hc : normalizer (D.centralQuotientPreimage U₁ : Set G) ≤
      normalizer (centralizer (D.centralQuotientPreimage U₁ : Set G) : Set G) :=
    le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer _)
  rw [conjugateSpan_eq_conjugateSpanBy, hsplit,
    conjugateSpanBy_sup_of_normalizes_seed _ _ _ hseed (inf_le_right.trans hc),
    ← conjugateSpan_eq_conjugateSpanBy] at hn
  exact hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
