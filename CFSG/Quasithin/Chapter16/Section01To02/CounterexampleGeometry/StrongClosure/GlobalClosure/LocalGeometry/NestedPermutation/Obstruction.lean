module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalGeometry.PairGeometry

/-!
# A diagnostic for the nested union-preservation inference

In D₈ × C₂, write r for the rotation of order four, s for a reflection and
c for the central generator of C₂. The factors ⟨s,c⟩ and ⟨r²,s,c⟩ satisfy
all the hypotheses of Aschbacher 3.4, and the first is contained in the second.
The rotation moves the first factor while preserving the second.

The elementary group calculations below use kernel-checked finite decisions.
The common central element c puts every conjugator in the intersection-generated
subgroup, so H = G. In particular this is not a minimal counterexample and does
not refute the source theorem or its assertion under minimality. It isolates
why preservation of the union alone cannot justify the printed step (b).

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4(b), printed p.94, DOI 10.1215/ijm/1256050927.
-/

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.NestedObstruction
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1

abbrev G := DihedralGroup 4 × Multiplicative (ZMod 2)

def small : Subgroup G where
  carrier := {x | x.1 = DihedralGroup.r 0 ∨ x.1 = DihedralGroup.sr 0}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

def large : Subgroup G where
  carrier := {x | x.1 = DihedralGroup.r 0 ∨ x.1 = DihedralGroup.r 2 ∨
    x.1 = DihedralGroup.sr 0 ∨ x.1 = DihedralGroup.sr 2}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

instance small_dec : DecidablePred (· ∈ small) :=
  inferInstanceAs (DecidablePred (fun x : G =>
    x.1 = DihedralGroup.r 0 ∨ x.1 = DihedralGroup.sr 0))

instance large_dec : DecidablePred (· ∈ large) :=
  inferInstanceAs (DecidablePred (fun x : G =>
    x.1 = DihedralGroup.r 0 ∨ x.1 = DihedralGroup.r 2 ∨
    x.1 = DihedralGroup.sr 0 ∨ x.1 = DihedralGroup.sr 2))

theorem nested : small ≤ large := by
  change ∀ x : G, x ∈ small → x ∈ large
  decide

theorem small_card : Nat.card small = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem small_sq : ∀ x : small, x ^ 2 = 1 := by decide

theorem rank_small : TwoRankAtLeastTwo small := by
  refine ⟨⊤, ?_, ?_⟩
  · simpa using small_card
  · intro x
    apply Subtype.ext
    exact small_sq x

theorem rank_large : TwoRankAtLeastTwo large := by
  refine ⟨small.subgroupOf large, ?_, ?_⟩
  · exact (Nat.card_congr (subgroupOfEquivOfLe nested).toEquiv).trans small_card
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((x : large) : G) ^ 2 = 1
    exact congrArg (fun y : small => (y : G)) (small_sq ⟨(x : large), x.property⟩)

def sylow : Sylow 2 G where
  toSubgroup := ⊤
  isPGroup' := IsPGroup.of_card (n := 4) (by
    rw [card_top, Nat.card_eq_fintype_card]
    decide)
  is_maximal' := by intro Q _ hQ; exact top_unique hQ

theorem generated_eq_top : intersectionGenerated small large = ⊤ := by
  apply top_unique
  intro g _
  apply transporter_mem_intersectionGenerated
    (a := (1, Multiplicative.ofAdd (1 : ZMod 2)))
  · exact Or.inl (show (1, Multiplicative.ofAdd (1 : ZMod 2)) ∈ small by decide)
  · decide
  · right
    have hh : ∀ g : G, g⁻¹ * (1, Multiplicative.ofAdd (1 : ZMod 2)) * g ∈ large := by
      decide
    exact hh g

theorem commutes : ⁅small, large⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  change ∀ a : G, a ∈ small → ∀ b : G, b ∈ large → b * a = a * b
  decide

theorem large_conj : ∀ x ∈ large, ∀ g : G, g⁻¹ * x * g ∈ large := by decide

theorem union_eq : (small : Set G) ∪ large = (large : Set G) :=
  Set.union_eq_right.mpr nested

theorem setup : Hypotheses sylow small large := by
  have hn₁ : large ≤ normalizer (small : Set G) := by
    change ∀ x : G, x ∈ large → ∀ y : G, y ∈ small ↔ x * y * x⁻¹ ∈ small
    decide
  have hn₂ : large ≤ normalizer (large : Set G) := le_normalizer
  refine ⟨le_top, le_top, commutes, rank_small, rank_large, ?_, ?_, ?_⟩
  · rw [union_eq, generated_eq_top]
    exact ⟨fun _ _ => ⟨mem_top _, mem_top _⟩, fun x hx g _ _ => large_conj x hx g⟩
  · rw [union_eq]
    exact ⟨fun _ hx => ⟨mem_top _, hn₁ hx⟩, fun x hx g _ _ => large_conj x hx g⟩
  · rw [union_eq]
    exact ⟨fun _ hx => ⟨mem_top _, hn₂ hx⟩, fun x hx g _ _ => large_conj x hx g⟩

def rotation : G := (DihedralGroup.r 1, 1)

theorem moves_small : conjugate small rotation ≠ small := by
  intro he
  have hh : (DihedralGroup.sr 2, 1) ∈ conjugate small rotation := by
    exact mem_map.mpr ⟨(DihedralGroup.sr 0, 1), by decide, by decide⟩
  rw [he] at hh
  exact (by decide : (DihedralGroup.sr 2, 1) ∉ small) hh

theorem no_swap : conjugate small rotation ≠ large := by
  intro he
  have hc : Nat.card (conjugate small rotation) = Nat.card small :=
    card_map_of_injective (MulAut.conj rotation⁻¹).injective
  rw [he, small_card] at hc
  have hl : Nat.card large = 8 := by rw [Nat.card_eq_fintype_card]; decide
  omega

theorem not_pair_permutation : ¬ (∀ s ∈ sylow,
    (conjugate small s = small ∧ conjugate large s = large) ∨
      (conjugate small s = large ∧ conjugate large s = small)) := by
  intro h
  rcases h rotation (mem_top _) with h | h
  · exact moves_small h.1
  · exact no_swap h.1

theorem not_counterexample : ¬ MinimalCounterexample sylow small large := by
  intro m
  exact m.fails (Or.inl generated_eq_top)

/-- The source setup and nesting do not by themselves imply pair permutation.
The same witness is explicitly excluded by minimal-counterexample failure. -/
public theorem exists_nested_hypotheses_without_pair_permutation :
    ∃ (S : Sylow 2 (DihedralGroup 4 × Multiplicative (ZMod 2)))
      (A₁ A₂ : Subgroup (DihedralGroup 4 × Multiplicative (ZMod 2))),
      Hypotheses S A₁ A₂ ∧ A₁ ≤ A₂ ∧ intersectionGenerated A₁ A₂ = ⊤ ∧
      ¬ MinimalCounterexample S A₁ A₂ ∧
      ¬ (∀ s ∈ S, (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
        (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁)) := by
  exact ⟨sylow, small, large, setup, nested, generated_eq_top,
    not_counterexample, not_pair_permutation⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.NestedObstruction
