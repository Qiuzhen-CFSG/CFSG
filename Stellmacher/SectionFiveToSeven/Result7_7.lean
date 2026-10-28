module

public import Stellmacher.SectionFiveToSeven.Result7_7.CentralizerTwo
public import Stellmacher.SectionFiveToSeven.Result7_7.LongerEndpoint

/-!
# Stellmacher (7.7): the subnormal-centralizer case

Suppose the next residual is subnormal in `C_G(Ω₁(Z(S)))`, whose 2-core
lies in `S`, and this centralizer is of characteristic two. Then the
initial center's centralizer commutes with `E_a O₂(E_{a+1})` modulo
`Q_a`; the centralizer of `V_{a+1}` is a 2-group; and for a longer
critical path the terminal residual escapes `C` and its center differs
from the next center.

The three companion modules prove these assertions separately. Subnormal
core monotonicity and (7.6)'s conjugate generation prove the commutator
bound. Residual stability makes the residual of the neighbor-center
centralizer globally normal and hence trivial. Finally residual
transitivity, critical minimality, and the residual-kernel criterion rule
out terminal containment. This module preserves the original three-field
public conclusion and assembles those proofs.

Source: B. Stellmacher, Journal of Algebra 190 (1997), (7.7), p.36;
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

public structure LemmaSevenSevenConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (C : Subgroup G) : Prop where
  centralizer_commutator :
    ⁅Subgroup.centralizer (z Γ cp.a : Set G),
      e Γ cp.a ⊔ twoCoreIn (e Γ cp.firstStep)⁆ ≤ q Γ cp.a
  next_v_centralizer_two :
    IsTwoGroup (Subgroup.centralizer (v Γ cp.firstStep : Set G))
  longer_endpoint :
    1 < cp.length →
      ¬ e Γ cp.a' ≤ C ∧ z Γ cp.a' ≠ z Γ cp.firstStep

/-- **Stellmacher (7.7).**  The characteristic-2 centralizer conclusions in
the case where the next residual is subnormal in `C_G(Ω₁(Z(S)))`. -/
public theorem lemma_seven_seven
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (C : Subgroup G)
    (hC : C = Subgroup.centralizer (omegaOneCenter S : Set G))
    (hsubnormal : SubnormalIn (e Γ cp.firstStep) C)
    (hcore : twoCoreIn C ≤ S)
    (hchar : Stellmacher.IsCharacteristicTwoType C) :
    LemmaSevenSevenConclusion Γ cp C := by
  exact
    { centralizer_commutator :=
        lemma_seven_seven_centralizer_commutator h Γ cp C hC hsubnormal hcore
      next_v_centralizer_two :=
        lemma_seven_seven_centralizer_two h Γ cp C hC hsubnormal hcore hchar
      longer_endpoint :=
        lemma_seven_seven_longer_endpoint h Γ cp C hC hsubnormal }

end Stellmacher.SectionsFiveToSeven
