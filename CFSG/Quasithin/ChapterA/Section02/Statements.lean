module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import CFSG.Quasithin.ChapterA.Section02.Statements.Sections
public import Theory.Quasithin.LocalRank
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# Exact statements and simultaneous induction for A.2.1–A.2.3

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.33–41 (PDF pp.44–52).

`TheoremA`, `TheoremB`, and `TheoremC` are propositions to be proved, not
asserted book theorems. K is the shared honest group-class parameter; the final
assembly must instantiate it with the full known-simple catalogue. The model
lists are actual-isomorphism predicates and do not certify their carriers.

The source's simple groups in B/C are nonabelian: the chapter introduction
(p.19) identifies C's groups as the nonabelian simple sections, and A.2.18–19
use that convention. Lean's `IsSimpleGroup` also includes cyclic prime-order
groups, so the nonabelian condition is explicit here. Semisimple in A means
E(S) = S, using the genuine component layer, not trivial solvable radical.

A retains both alternatives for local prime rank and the ordinary-rank bound
when mₚ(G) ≤ 2. Its exception uses a subgroup H of G, the actual quotient by
Z(H), and two components *of H*. Their embedded centers agree in H. The
product condition is an ordered product decomposition, not merely generation.

The induction predicates quantify over strictly smaller sections and retain
each theorem's own hypotheses. No inheritance of quasithinness to arbitrary
quotients is assumed. The final theorem below proves the logical simultaneous
induction scheme; its step is an explicit premise to be discharged by A.2's
structural and family arguments. The other bridges use the subgroup rank
inequality to rule out the exception when mₚ(G) ≤ 2.
-/

@[expose] public section

universe u v

namespace CFSG.Quasithin.ChapterA.Section02

open Theory.GroupTheory

/-- The source condition S = E(S), including the trivial semisimple group. -/
def IsSemisimple (S : Type u) [Group S] : Prop := componentLayer S = ⊤

/-- The two actual components and all parameters of A(1.b). The center
equality is between subgroups of H, not between abstract center types. -/
structure TheoremAUnitaryPair (H : Type u) [Group H] where
  first : Subgroup H
  second : Subgroup H
  first_component : IsComponent H first
  second_component : IsComponent H second
  product : ∀ h : H, ∃ a : first, ∃ b : second, (a : H) * (b : H) = h
  n₁ : ℕ
  n₂ : ℕ
  first_large : 3 ≤ n₁
  second_large : 3 ≤ n₂
  first_odd : Odd n₁
  second_odd : Odd n₂
  first_model : IsSpecialUnitaryModel first 3 (2 ^ n₁)
  second_model : IsSpecialUnitaryModel second 3 (2 ^ n₂)
  centers_eq : (Subgroup.center first).map first.subtype =
    (Subgroup.center second).map second.subtype
  gcd_eq : Nat.gcd n₁ n₂ = 1 ∨ Nat.gcd n₁ n₂ = 3

/-- All clauses of the exceptional alternative A(1.b). -/
def TheoremAException (G : Type u) (S : Type v) [Group G] [Group S] (p : ℕ) : Prop :=
  p = 3 ∧ ∃ H : Subgroup G, primeRank 3 H = 3 ∧
    Nonempty (S ≃* (H ⧸ Subgroup.center H)) ∧ Nonempty (TheoremAUnitaryPair H)

/-- Both numbered conclusions of A for one section and one odd prime. -/
def TheoremAConclusion (G : Type u) (S : Type v) [Group G] [Group S] (p : ℕ) : Prop :=
  ((twoLocalPrimeRank p S ≤ twoLocalPrimeRank p G ∧ twoLocalPrimeRank p G ≤ 2) ∨
    TheoremAException G S p) ∧
  (primeRank p G ≤ 2 → primeRank p S ≤ primeRank p G)

/-- Theorem A.2.1 as a proposition, with the shared K parameter. -/
def TheoremA (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  IsQuasithin G → IsKGroup K G →
    ∀ (S : Type u) [Group S] [Finite S], IsSectionOf S G → IsSemisimple S →
      ∀ p : ℕ, p.Prime → Odd p → TheoremAConclusion G S p

/-- Theorem A.2.2 as a proposition. Nonabelian simplicity is explicit. -/
def TheoremB (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G → ¬ IsMulCommutative G → IsQuasithin G → IsKGroup K G →
    IsTheoremBModel G

/-- Theorem A.2.3 as a proposition, using ordinary odd-prime ranks. -/
def TheoremC (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G → ¬ IsMulCommutative G → IsStronglyQuasithin G → IsKGroup K G →
    IsTheoremCModel G

/-- The three assertions that are proved simultaneously in A.2. -/
def TheoremsABC (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  TheoremA K G ∧ TheoremB K G ∧ TheoremC K G

/-- The minimality premise in A.2.8–A.2.11. The quasithin and K hypotheses
remain inside `TheoremA`, so nonquasithin sections impose no requirement. -/
def TheoremAOnProperSections (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsProperSectionOf H G → TheoremA K H

/-- The simultaneous induction hypothesis from printed p.35. -/
def TheoremsOnProperSections (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsProperSectionOf H G → TheoremsABC K H

/-- A counterexample with all source hypotheses, for the early A reductions. -/
def CounterexampleToTheoremA (K : GroupClass.{u}) (G S : Type u)
    [Group G] [Group S] [Finite G] [Finite S] (p : ℕ) : Prop :=
  IsQuasithin G ∧ IsKGroup K G ∧ IsSectionOf S G ∧ IsSemisimple S ∧
    p.Prime ∧ Odd p ∧ ¬ TheoremAConclusion G S p

/-- The minimal counterexample hypothesis used in A.2.12–A.2.19. -/
def MinimalCounterexample (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  ¬ TheoremsABC K G ∧ TheoremsOnProperSections K G

variable {G : Type u} {S : Type v} [Group G] [Group S]

theorem TheoremAUnitaryPair.generates (d : TheoremAUnitaryPair G) : d.first ⊔ d.second = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨a, b, rfl⟩ := d.product g
  exact (d.first ⊔ d.second).mul_mem
    ((show d.first ≤ d.first ⊔ d.second from le_sup_left) a.property)
    ((show d.second ≤ d.first ⊔ d.second from le_sup_right) b.property)

theorem TheoremAUnitaryPair.semisimple (d : TheoremAUnitaryPair G) : IsSemisimple G := by
  apply top_unique
  rw [← d.generates]
  exact sup_le (le_sSup d.first_component) (le_sSup d.second_component)

theorem TheoremAException.primeRank_ge_three [Finite G] {p : ℕ}
    (h : TheoremAException G S p) : 3 ≤ primeRank p G := by
  obtain ⟨rfl, H, hH, _, _⟩ := h
  exact hH.ge.trans (primeRank_le_of_injective 3 H.subtype H.subtype_injective)

theorem not_theoremAException_of_primeRank_le_two [Finite G] {p : ℕ}
    (h : primeRank p G ≤ 2) : ¬ TheoremAException G S p := by
  intro he
  exact (by decide : ¬ 3 ≤ 2) (he.primeRank_ge_three.trans h)

/-- When the ordinary rank is at most two, A gives both rank inequalities;
the exceptional alternative is impossible by the rank of its subgroup H. -/
theorem TheoremAConclusion.ranks_of_primeRank_le_two [Finite G] {p : ℕ}
    (h : TheoremAConclusion G S p) (hr : primeRank p G ≤ 2) :
    twoLocalPrimeRank p S ≤ twoLocalPrimeRank p G ∧ primeRank p S ≤ primeRank p G :=
  ⟨(h.1.resolve_right (not_theoremAException_of_primeRank_le_two hr)).1, h.2 hr⟩

theorem TheoremAException.of_mulEquiv {T : Type u} [Group T] {p : ℕ}
    (h : TheoremAException G S p) (e : T ≃* S) : TheoremAException G T p := by
  obtain ⟨hp, H, hr, iso, pair⟩ := h
  exact ⟨hp, H, hr, iso.map (fun a => e.trans a), pair⟩

/-- Isomorphism invariance of the shared local-rank invariant. -/
theorem twoLocalPrimeRank_mulEquiv [Finite G] [Finite S] (p : ℕ) (e : G ≃* S) :
    twoLocalPrimeRank p G = twoLocalPrimeRank p S := by
  apply le_antisymm
  · apply (twoLocalPrimeRank_le_iff p _).mpr
    intro M hM
    have h := (isTwoLocal_map e hM).primeRank_le p
    rwa [← primeRank_equiv p (Subgroup.equivMapOfInjective M e.toMonoidHom e.injective)] at h
  · apply (twoLocalPrimeRank_le_iff p _).mpr
    intro M hM
    have h := (isTwoLocal_map e.symm hM).primeRank_le p
    rwa [← primeRank_equiv p
      (Subgroup.equivMapOfInjective M e.symm.toMonoidHom e.symm.injective)] at h

theorem TheoremAConclusion.of_mulEquiv [Finite G] [Finite S]
    {T : Type u} [Group T] [Finite T] {p : ℕ}
    (h : TheoremAConclusion G S p) (e : T ≃* S) : TheoremAConclusion G T p := by
  refine ⟨?_, ?_⟩
  · rcases h.1 with hl | he
    · exact .inl ⟨(twoLocalPrimeRank_mulEquiv p e).trans_le hl.1, hl.2⟩
    · exact .inr (he.of_mulEquiv e)
  · intro hr
    exact (primeRank_equiv p e).trans_le (h.2 hr)

variable {K : GroupClass.{u}} {H : Type u} [Group H] [Finite G] [Finite H]

/-- The explicitly stated 'in particular' conclusion of A(2). -/
theorem TheoremA.stronglyQuasithin_section (hA : TheoremA K G)
    (hG : IsStronglyQuasithin G) (hK : IsKGroup K G)
    (hHG : IsSectionOf H G) (hH : IsSemisimple H) : IsStronglyQuasithin H := by
  intro p hp ho
  exact ((hA hG.quasithin hK H hHG hH p hp ho).2 (hG p hp ho)).trans (hG p hp ho)

/-- A strongly quasithin ambient group also forces the nonexceptional local
alternative for every semisimple section. -/
theorem TheoremA.localRanks_of_stronglyQuasithin (hA : TheoremA K G)
    (hG : IsStronglyQuasithin G) (hK : IsKGroup K G)
    (hHG : IsSectionOf H G) (hH : IsSemisimple H) (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    twoLocalPrimeRank p H ≤ twoLocalPrimeRank p G :=
  ((hA hG.quasithin hK H hHG hH p hp ho).ranks_of_primeRank_le_two (hG p hp ho)).1

theorem TheoremsOnProperSections.theoremA (ih : TheoremsOnProperSections K G) :
    TheoremAOnProperSections K G := fun H _ _ hH => (ih H hH).1

theorem TheoremsOnProperSections.subgroup (ih : TheoremsOnProperSections K G)
    (U : Subgroup G) (hU : U ≠ ⊤) : TheoremsABC K U :=
  ih U (IsProperSectionOf.subgroup U hU)

theorem TheoremsOnProperSections.quotient (ih : TheoremsOnProperSections K G)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : TheoremsABC K (G ⧸ N) :=
  ih (G ⧸ N) (IsProperSectionOf.quotient N hN)

theorem TheoremsOnProperSections.section_of_proper_subgroup
    (ih : TheoremsOnProperSections K G) {U : Subgroup G} (hU : U ≠ ⊤)
    (hHU : IsSectionOf H U) : TheoremsABC K H :=
  ih H (hHU.proper_of_proper_subgroup hU)

/-- C's asserted result supplies B's output on the strongly quasithin domain;
this does not assert either classification theorem. -/
theorem TheoremC.theoremBOutput (hC : TheoremC K G) (hs : IsSimpleGroup G)
    (hna : ¬ IsMulCommutative G) (hG : IsStronglyQuasithin G) (hK : IsKGroup K G) :
    IsTheoremBModel G := (hC hs hna hG hK).toTheoremBModel

/-- Failure of the simultaneous assertion has one of the three source owners. -/
theorem not_theoremsABC_iff :
    ¬ TheoremsABC K G ↔ ¬ TheoremA K G ∨ ¬ TheoremB K G ∨ ¬ TheoremC K G := by
  simp only [TheoremsABC, not_and_or]

/-- The logical induction scheme for A.2. Its premise is the still-to-be-proved
structural induction step, not a proof substitute for the book theorems. -/
theorem simultaneous_induction
    (step : ∀ (X : Type u) [Group X] [Finite X],
      TheoremsOnProperSections K X → TheoremsABC K X) : TheoremsABC K G := by
  have all : ∀ n : ℕ, ∀ (X : Type u) [Group X] [Finite X],
      Nat.card X = n → TheoremsABC K X := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X _ _ hcard
      apply step X
      intro Y _ _ hY
      exact ih (Nat.card Y) (hcard ▸ hY.2) Y rfl
  exact all (Nat.card G) G rfl

end CFSG.Quasithin.ChapterA.Section02
