module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar.LowRank
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.BinarySymplectic

/-!
# Reduction of the polar contribution to the B.1.13 Sylow fixer

The published model predicate has five alternatives. The low-rank comparison
proofs handle the small symplectic and orthogonal parameters, and the binary
symplectic derived endpoint uses its full automorphism fixer theorem. The odd
orthogonal–symplectic equivalence works at every rank, leaving exactly three
families of rank at least three, each with an actual carrier isomorphism.

This module proves that exhaustive reduction and applies it to the literal
component central quotient. It does not yet prove the full polar fixer bound:
the higher-rank symplectic, split orthogonal and minus orthogonal calculations
remain to be supplied before final assembly. Finiteness, simplicity and
perfectness for those calculations may be inherited from the source component.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar

/-- The three remaining polar families, with actual isomorphisms and all ranks
at least three. Odd orthogonal groups have already been compared with PSp. -/
inductive HigherRankModel (X : Type*) [Group X] : Prop
  | symplectic (r f : ℕ) (hr : 3 ≤ r) (hf : 0 < f)
      (model : ClassicalGroup.IsPSp X r (2 ^ f))
  | orthogonalPlus (r f : ℕ) (hr : 3 ≤ r) (hf : 0 < f)
      (model : ClassicalGroup.IsPOmegaPlus X r (2 ^ f))
  | orthogonalMinus (r f : ℕ) (hr : 3 ≤ r) (hf : 0 < f)
      (model : ClassicalGroup.IsPOmegaMinus X r (2 ^ f))

/-- Exhaustive reduction of the published polar model predicate: all low ranks
and the binary derived endpoint are proved; the remaining models have rank ≥ 3.
This is a reduction, not the unfinished full-family fixer theorem. -/
theorem fixer_or_higherRank {X : Type*} [Group X] [Finite X]
    (hmodel : SymplecticOrthogonalModel X) :
    SylowFixerIsTwoGroup X ∨ HigherRankModel X := by
  cases hmodel with
  | symplectic r f hf hp hm =>
    by_cases hr : r ≤ 2
    · exact .inl (symplectic_smallRank_model_fixer hf hp hr hm)
    · exact .inr (.symplectic r f (by omega) hf hm)
  | orthogonalPlus r f hf hp hm =>
    exact .inr (.orthogonalPlus r f hp.2 hf hm)
  | orthogonalOdd r f hf hp hm =>
    have hs := odd_model_isPSp hp.2.1 hm
    by_cases hr : r ≤ 2
    · exact .inl (symplectic_smallRank_model_fixer hf hp hr hs)
    · exact .inr (.symplectic r f (by omega) hf hs)
  | orthogonalMinus r f hf hp hm =>
    by_cases hr : r = 2
    · subst r
      exact .inl (minusTwo_model_fixer hf hm)
    · exact .inr (.orthogonalMinus r f (by have := hp.2; omega) hf hm)
  | symplecticDerived he =>
    obtain ⟨e⟩ := he
    exact .inl (fixer_of_equiv e binarySymplecticDerived_fixer)

/-- In B.1.13 itself, the actual component quotient either gives the requested
containment or lies in one of the three remaining higher-rank families.
The perfect-central-cover transport uses precisely the source quotient. -/
theorem le_component_or_higherRank {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G))
    (hmodel : SymplecticOrthogonalModel (L ⧸ center L))
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥) :
    K ≤ L ∨ HigherRankModel (L ⧸ center L) := by
  rcases fixer_or_higherRank hmodel with hfix | hhigh
  · exact .inl (le_component_of_quotient_model K L T hL hLK hkind hKN
      (MulEquiv.refl _) hfix hd)
  · exact .inr hhigh

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar
