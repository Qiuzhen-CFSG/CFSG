module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.Inputs
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements

/-!+# Earlier source clauses for the exceptional table reduction

These are explicit inputs, not assertions of the earlier theorems. The center
clause is the specialization of 16.1.2(2) to the three sporadics occurring in
16.3.5(2). The automorphism clauses retain the actual carriers and the complete
fixed subgroups of 16.1.5(4),(8),(11). In particular a fixed subgroup on the
central quotient is not replaced by the image of a fixed subgroup upstairs.

The Rudvalis extension has a normal elementary kernel of order 32, followed
by a normal elementary kernel of order 64 in its quotient, then S₅. It asserts
neither a splitting nor that either kernel is self-centralizing. The existing
M₁₂ and J₂ definitions retain their actual quaternion central-product kernels.
No inner-index bound, component exclusion, or non-2-central mark is an input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2 and 16.1.5, printed pp.1170–1172 / PDF pp.1187–1189.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
open Subgroup Theory.GroupTheory ClassificationModels

/-- The three actual central quotients in the exceptional enlargement. -/
def ExceptionalQuotient (H : Type*) [Group H] : Prop :=
  Nonempty ((H ⧸ center H) ≃* SporadicName.m12.Carrier) ∨
  Nonempty ((H ⧸ center H) ≃* SporadicName.j2.Carrier) ∨
  Nonempty ((H ⧸ center H) ≃* SporadicName.ru.Carrier)

/-- The applicable specialization of the center bound in 16.1.2(2). -/
def CenterClause {G : Type*} [Group G] [Finite G] (𝒦 : GroupClass) : Prop :=
  Hypothesis1611 𝒦 G → ∀ (i : G) (I : Subgroup G), orderOf i = 2 →
    IsCentralizerComponent i I → ExceptionalQuotient I → Nat.card (center I) ≤ 2

abbrev C2 := Multiplicative (ZMod 2)
abbrev Elementary (n : ℕ) := Fin n → C2
noncomputable abbrev SzEight := BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1

/-- The successive normal kernels in S₅/E₆₄/E₃₂; slash denotes extension. -/
def IsRudvalisExtension (C : Type*) [Group C] : Prop :=
  ∃ (N : Subgroup C) (_ : N.Normal), Nonempty (N ≃* Elementary 5) ∧
    ∃ (P : Subgroup (C ⧸ N)) (_ : P.Normal),
      Nonempty (P ≃* Elementary 6) ∧
      Nonempty (((C ⧸ N) ⧸ P) ≃* Equiv.Perm (Fin 5))

/-- Both literal alternatives of 16.1.5(11), including innerness. -/
def RudvalisInvolutionAlternative (r : MulAut SporadicName.ru.Carrier) : Prop :=
  (∃ g, r = MulAut.conj g) ∧
    (IsRudvalisExtension r.fixedSubgroup ∨
      Nonempty (r.fixedSubgroup ≃* Elementary 2 × SzEight))

/-- The exact earlier involution rows allowed in the conditional reduction. -/
structure InvolutionTables : Prop where
  m12 : ∀ r : MulAut SporadicName.m12.Carrier, orderOf r = 2 →
    OtherPreliminaries.Mathieu.M12InvolutionAlternative r
  j2 : ∀ r : MulAut SporadicName.j2.Carrier, orderOf r = 2 →
    OtherPreliminaries.JankoTwoHigmanSims.J2InvolutionAlternative r
  ru : ∀ r : MulAut SporadicName.ru.Carrier, orderOf r = 2 →
    RudvalisInvolutionAlternative r

end CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
