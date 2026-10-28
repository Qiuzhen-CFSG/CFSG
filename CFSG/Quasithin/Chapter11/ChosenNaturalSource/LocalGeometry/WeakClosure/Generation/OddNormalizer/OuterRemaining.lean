module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterOddThree
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterMcLaughlin

/-!
# The exact remaining outer component rows

The ternary Frattini argument excludes odd PSL₃ and PSU₃, and the native
McL word excludes the final sporadic outer row. Combined with the earlier
exclusions, an actual outer section now requires Sp₆(2), odd PSp₄ or G₂,
or the specified Fermat-linear or Mersenne-unitary four-dimensional row.
Every alternative retains an actual model equivalence and its source parameters.
The original cover, module and normalizer remain those in Source.

These remaining outer rows and the moved J₄ local inspection belong to
qt-d-1222-natural-odd-kernel-normalizer. The ordinary C.2.8 exclusion belongs
to qt-d-1222-natural-point-fixed-summand. Final 11.2.1 assembly belongs to
qt-d-1222-natural-weak-closure-source.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

/-- The five surviving actual model rows for an outer section. -/
def RemainingOuterModel (Q : Type*) [Group Q] : Prop :=
  ClassicalGroup.IsPSp Q 3 2 ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSp Q 2 p) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassificationModels.IsG2At Q p) ∨
    (∃ r : ℕ, r.Prime ∧ (∃ k : ℕ, r = 2 ^ (2 ^ k) + 1) ∧
      ClassicalGroup.IsPSL Q 4 r) ∨
    (∃ s : ℕ, s.Prime ∧ (∃ b : ℕ, s + 1 = 2 ^ b) ∧
      ClassicalGroup.IsPSU Q 4 s)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The full Theorem B catalogue leaves exactly these five outer rows. -/
theorem moved_outer_remaining_models {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f) : RemainingOuterModel (K ⧸ center K) := by
  obtain ⟨hC,hAlt,hL2⟩ := moved_outer_section_exclusions D S K hK ho
  have h3 {q : ℕ} (hq : Odd q) := moved_outer_not_odd_three D S K hK hm ho hq
  have hU4 {n : ℕ} (hn : 1 ≤ n) (h : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) :
      False := moved_outer_not_binary_unitary_four D S K hK ho hn h
  have hU5 := moved_outer_not_unitary_five_four D S K hK ho
  unfold RemainingOuterModel
  cases hm with
  | alternating n _ he => exact (hAlt n he).elim
  | odd h =>
    cases h with
    | linear_two q hq he => exact (hL2 q hq he).elim
    | linear_three p a _ hp _ he => exact ((h3 hp.pow).1 he).elim
    | unitary_three p a _ hp _ he => exact ((h3 hp.pow).2 he).elim
    | symplectic p hp hodd he => exact Or.inr (Or.inl ⟨p,hp,hodd,he⟩)
    | g2 p hp hodd he => exact Or.inr (Or.inr (Or.inl ⟨p,hp,hodd,he⟩))
    | linear_four p hp hF he => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p,hp,hF,he⟩)))
    | unitary_four p hp hM he => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p,hp,hM,he⟩)))
  | bender h => exact (hC (.bender h)).elim
  | linear_binary n hn h => exact (hC (.linear_binary n hn h)).elim
  | symplectic_binary h => exact Or.inl h
  | rank_two n h =>
    cases h with
    | linear hn h => exact (hC (.rank_two n (.linear hn h))).elim
    | unitary_four hn h => exact (hU4 hn h).elim
    | unitary_five hn h => subst n; exact (hU5 h).elim
    | symplectic hn h => exact (hC (.rank_two n (.symplectic hn h))).elim
    | g2 hn h => exact (hC (.rank_two n (.g2 hn h))).elim
    | triality hn h => exact (hC (.rank_two n (.triality hn h))).elim
    | ree_f4 m hm hn h => exact (hC (.rank_two n (.ree_f4 m hm hn h))).elim
    | symplectic_derived hn h => exact (hC (.rank_two n (.symplectic_derived hn h))).elim
    | g2_derived hn h => exact (hC (.rank_two n (.g2_derived hn h))).elim
    | tits hn h => exact (hC (.rank_two n (.tits hn h))).elim
  | sporadic h =>
    rcases h with ⟨name,he⟩ | he | he
    · by_cases hj : name = .j3
      · subst name
        exact (moved_outer_not_janko_three D S K hK ho he.some).elim
      · exact (hC (.sporadic (.inl ⟨name,hj,he⟩))).elim
    · exact (hC (.sporadic (.inr he))).elim
    · exact (moved_outer_not_mcl D S K hK ho he.some).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
