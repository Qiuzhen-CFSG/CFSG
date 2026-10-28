module

public import Theory.GroupTheory.PGroup.OmegaCoprimeAction
public import Theory.GroupTheory.NormalCentralQuotientAction.Normalizer

/-!
# A two-group fixing the first omega layer of an odd core

Suppose L is normal, O₂(L) ≤ R, and R is a two-group. If the p-core Q of
L/O₂(L) is self-centralizing and is either abelian or of exponent p, then
fixation of Ω₁(Q) by R implies that L normalizes R. The abelian branch uses
coprime action on Ω₁; the exponent-p branch has Ω₁(Q) = Q. The characteristic
restriction kernel gives triviality on L/O₂(L), and the normalizer lemma
lifts the result to the original groups.

This supplies the corrected single-odd-prime step in Aschbacher–Smith,
Proposition 1.3.8, combined manuscript of 1 March 2004, printed p.513.
The actual radical argument must establish the centralizer and fixed-point
premises from its local structure; they are explicit here.
-/

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The single-prime normality step, including higher-exponent abelian cores. -/
public theorem le_normalizer_of_twoGroup_fixes_omega
    (L R : Subgroup G) [L.Normal] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hR : IsPGroup 2 R) (hcore : (pCore 2 L).map L.subtype ≤ R)
    (hshape : IsMulCommutative (pCore p (L ⧸ pCore 2 L)) ∨
      ∀ x : pCore p (L ⧸ pCore 2 L), x ^ p = 1)
    (hcentral : centralizer (pCore p (L ⧸ pCore 2 L) : Set (L ⧸ pCore 2 L)) ≤
      pCore p (L ⧸ pCore 2 L))
    (hfix : ∀ r : R, ∀ x ∈ omega (pCore p (L ⧸ pCore 2 L)) (p := p) 1,
      normalQuotientAction L (pCore 2 L) r (x : L ⧸ pCore 2 L) = x) :
    L ≤ normalizer (R : Set G) := by
  let Q := pCore p (L ⧸ pCore 2 L)
  let ρ : R →* MulAut (L ⧸ pCore 2 L) :=
    (normalQuotientAction L (pCore 2 L)).comp R.subtype
  have hp2 : p ≠ 2 := by
    intro he
    exact (by decide : ¬ Odd 2) (he ▸ hp)
  have ht : ∀ r : R, ρ r = 1 := by
    rcases hshape with habelian | hexponent
    · let := habelian
      exact OmegaAction.action_eq_one_of_fixes_omegaOne_selfCentralizing Q
        pCore_isPGroup hR hp2 hcentral ρ hfix
    · apply action_eq_one_of_fixes_selfCentralizing Q pCore_isPGroup hR
        (Nat.coprime_two_right.mpr hp) hcentral ρ
      intro r
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      apply hfix r x
      apply subset_closure
      change x ^ (p ^ 1) = 1
      simpa only [pow_one] using hexponent x
  exact le_normalizer_of_trivial_normalQuotientAction L R (pCore 2 L) hcore
    (fun r hr => ht ⟨r, hr⟩)

end Subgroup
