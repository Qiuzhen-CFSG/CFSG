module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Transport
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Linear
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Suzuki
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Unitary
public import BenderSuzuki.External.Hall.Basic

/-!
# Terminal-factor rigidity reduced to the simple Bender quotient

Intersect the fixed Sylow subgroup with the normal terminal span. The two
factors lie in this Sylow intersection by the explicit placement hypotheses.
Their images modulo the odd core still commute, contain elementary four-groups,
and have strongly closed union. The quotient map is injective on the Sylow
intersection, so nesting of the images gives nesting of the whole factors.

The concrete linear, Suzuki and unitary rigidity theorems discharge every
model premise. Only the two independent source-placement hypotheses remain
explicit in `terminal_factors_nested_of_le_span`. Involution containment alone
is never used to infer containment of a factor.

Source: M. Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
pp.94–96, final paragraph p.96; GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Lift the concrete quotient rigidity through the terminal odd core. -/
theorem terminal_factors_nested_of_quotient_rigidity
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (h₁L : A₁ ≤ closure (terminalInvolutions A₁ A₂))
    (h₂L : A₂ ≤ closure (terminalInvolutions A₁ A₂))
    (hr : InternalRigidity.SylowFactorRigidity
      ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂)))) :
    A₁ ≤ A₂ ∨ A₂ ≤ A₁ := by
  let L := closure (terminalInvolutions A₁ A₂)
  let : L.Normal := (terminalInvolutions_productDisconnected h f hp).closure_normal
  let P : Sylow 2 L := BenderSuzuki.External.hallSylowSubgroupOfNormal S L
  let B := A₁.subgroupOf L
  let C := A₂.subgroupOf L
  have hBP : B ≤ (P : Subgroup L) := fun x hx => h.left_le hx
  have hCP : C ≤ (P : Subgroup L) := fun x hx => h.right_le hx
  have hBC : ⁅B, C⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    apply Subtype.ext
    exact mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp h.commute) hx) y hy
  have hB : TwoRankAtLeastTwo B :=
    InternalRigidity.rank_map_of_injective
      (subgroupOfEquivOfLe h₁L).symm.toMonoidHom
      (subgroupOfEquivOfLe h₁L).symm.injective h.left_rank
  have hC : TwoRankAtLeastTwo C :=
    InternalRigidity.rank_map_of_injective
      (subgroupOfEquivOfLe h₂L).symm.toMonoidHom
      (subgroupOfEquivOfLe h₂L).symm.injective h.right_rank
  have hc : IsStronglyClosedSet ((B : Set L) ∪ C) (P : Subgroup L) ⊤ := by
    refine ⟨fun x hx => hx.elim (hBP ·) (hCP ·), ?_⟩
    intro x hx g _ hxg
    exact f.closed.2 (x : G) hx (g : G) (mem_top _) hxg
  let O := pPrimeCore 2 L
  let q := QuotientGroup.mk' O
  have hq : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact pPrimeCore_coprime_card
  have hrL : InternalRigidity.SylowFactorRigidity L :=
    InternalRigidity.rigidity_of_surjective_coprime q
      (QuotientGroup.mk'_surjective O) hq hr
  rcases hrL P B C hBP hCP hBC hB hC hc with hn | hn
  · left
    intro x hx
    exact hn (show (⟨x, h₁L hx⟩ : L) ∈ B from hx)
  · right
    intro x hx
    exact hn (show (⟨x, h₂L hx⟩ : L) ∈ C from hx)

/-- ZD identifies the actual quotient to which the remaining model theorem applies. -/
theorem terminal_factors_nested_of_simple_bender_rigidity
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (h₁L : A₁ ≤ closure (terminalInvolutions A₁ A₂))
    (h₂L : A₂ ≤ closure (terminalInvolutions A₁ A₂))
    (hr : BenderSuzuki.IsSimpleBenderGroup
      ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →
      InternalRigidity.SylowFactorRigidity
        ((closure (terminalInvolutions A₁ A₂)) ⧸
          pPrimeCore 2 (closure (terminalInvolutions A₁ A₂)))) :
    A₁ ≤ A₂ ∨ A₂ ≤ A₁ := by
  exact terminal_factors_nested_of_quotient_rigidity h f hp h₁L h₂L
    (hr (terminal_structure_perfect_bender h.left_rank hs).2)


/-- Reduce internal rigidity to its two remaining concrete model families.
The PSL₂ family and all quotient and Sylow transports are discharged here. -/
theorem terminal_factors_nested_of_nonlinear_models
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (h₁L : A₁ ≤ closure (terminalInvolutions A₁ A₂))
    (h₂L : A₂ ≤ closure (terminalInvolutions A₁ A₂))
    (hSuz : ∀ n : ℕ, 1 ≤ n →
      InternalRigidity.SylowFactorRigidity (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n))
    (hUni : ∀ n : ℕ, 2 ≤ n → ∀ (E : Type) [Field E] [Finite E]
      (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E),
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
      Nat.card E = (2 ^ n) ^ 2 → Nat.card {z : E // J.conj z = z} = 2 ^ n →
      InternalRigidity.SylowFactorRigidity
        (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) :
    A₁ ≤ A₂ ∨ A₂ ≤ A₁ := by
  apply terminal_factors_nested_of_simple_bender_rigidity h f hp hs h₁L h₂L
  intro hm
  rcases hm with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨n, hn, ⟨e⟩⟩⟩ |
    ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, ⟨e⟩⟩⟩
  · exact InternalRigidity.rigidity_of_mulEquiv e (InternalRigidity.linear_rigidity n hn)
  · exact InternalRigidity.rigidity_of_mulEquiv e (hSuz n hn)
  · exact InternalRigidity.rigidity_of_mulEquiv e (hUni n hn E J hJ hEcard hfixedCard)

/-- Whole terminal factors lying in the involution span are nested.
The concrete Bender models and the odd-core transport are fully discharged;
placement in the span remains an independent source input. -/
theorem terminal_factors_nested_of_le_span
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (h₁L : A₁ ≤ closure (terminalInvolutions A₁ A₂))
    (h₂L : A₂ ≤ closure (terminalInvolutions A₁ A₂)) :
    A₁ ≤ A₂ ∨ A₂ ≤ A₁ := by
  exact terminal_factors_nested_of_nonlinear_models h f hp hs h₁L h₂L
    InternalRigidity.suzuki_rigidity InternalRigidity.unitary_rigidity

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end
