module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Models
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Transport
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.SmallRank
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.OddComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison

/-!
# Low polar ranks and the odd orthogonal comparison for B.1.13

The actual PSp₂–PSL₂ equivalence gives the rank-one fixer bound, while the
published four-dimensional result covers the permitted rank-two symplectic
parameters. Projection off the polar radical identifies every odd orthogonal
carrier in characteristic two with its symplectic carrier; this also proves
the odd rank-one and rank-two cases. The genuine minus-four/PSL₂(q²)
equivalence covers rank two in the minus family, including q = 2.

Each bound concerns the entire pointwise automorphism fixer. The component
applications use the literal central quotient and discharge the Sylow-fixer
premise of the B.1.13 containment argument. The model comparisons are reused
from the imported Theory modules, with their original source and licensing
attribution. No order comparison is substituted for a carrier equivalence.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74 of `refs/quasithin.pdf`;
GLS3 §2.7 for the classical aliases and projective conventions.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar

variable {X : Type*} [Group X]

/-- The rank-one symplectic fixer, through the actual central-quotient equivalence. -/
theorem symplecticOne_fixer (F : Type*) [Field F] [Finite F] [CharP F 2] :
    SylowFixerIsTwoGroup (ClassicalGroup.PSp 1 F) :=
  fixer_of_equiv Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv
    linearTwo_fixer

/-- The rank-one alias in the published model predicate. -/
theorem symplecticOne_model_fixer [Finite X] {f : ℕ}
    (hmodel : ClassicalGroup.IsPSp X 1 (2 ^ f)) : SylowFixerIsTwoGroup X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact fixer_of_equiv e (symplecticOne_fixer F)

/-- Both allowed symplectic ranks at most two, with the published exclusions.
The forbidden full PSp₄(2) is not confused with its derived subgroup. -/
theorem symplectic_smallRank_model_fixer [Finite X] {r f : ℕ}
    (hf : 0 < f) (hp : KnownSimple.SymplecticParameters r (2 ^ f)) (hr : r ≤ 2)
    (hmodel : ClassicalGroup.IsPSp X r (2 ^ f)) : SylowFixerIsTwoGroup X := by
  rcases hp with ⟨_, hrpos, _, hbinary⟩
  by_cases h1 : r = 1
  · subst r
    exact symplecticOne_model_fixer hmodel
  · have h2 : r = 2 := by omega
    subst r
    have hf1 : f ≠ 1 := by
      intro h
      exact hbinary rfl (by simp [h])
    exact symplecticFour_model_fixer (by omega) hmodel

/-- In characteristic two, projection off the polar radical identifies the
literal odd orthogonal scalar quotient with the literal symplectic central quotient. -/
theorem odd_model_isPSp {r f : ℕ} (hr : 0 < r)
    (hmodel : ClassicalGroup.IsPOmegaOdd X r (2 ^ f)) :
    ClassicalGroup.IsPSp X r (2 ^ f) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.oddProjectiveEquivPSp hr)⟩⟩

/-- The odd rank-one and rank-two cases have exactly the symplectic exclusions. -/
theorem odd_smallRank_model_fixer [Finite X] {r f : ℕ}
    (hf : 0 < f) (hp : KnownSimple.OrthogonalOddParameters r (2 ^ f)) (hr : r ≤ 2)
    (hmodel : ClassicalGroup.IsPOmegaOdd X r (2 ^ f)) : SylowFixerIsTwoGroup X :=
  symplectic_smallRank_model_fixer hf hp hr (odd_model_isPSp hp.2.1 hmodel)

/-- The minus-four calculation includes q = 2, using PSL₂ over the quadratic
extension, not a conclusion inferred from equal orders. -/
theorem minusTwo_fixer (F : Type*) [Field F] [Finite F] {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f) :
    SylowFixerIsTwoGroup (ClassicalGroup.POmegaMinus 2 F) :=
  fixer_of_equiv (ClassicalOrthogonal.TheoremDRootNormalizer.minusTwoEquivPSL F hf hF)
    linearTwo_fixer

/-- The literal rank-two minus model at every positive binary exponent. -/
theorem minusTwo_model_fixer [Finite X] {f : ℕ} (hf : 0 < f)
    (hmodel : ClassicalGroup.IsPOmegaMinus X 2 (2 ^ f)) : SylowFixerIsTwoGroup X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  exact fixer_of_equiv e (minusTwo_fixer F hf hF)

section Applications
variable {G : Type*} [Group G] [Finite G]
  (K L : Subgroup G) (T : Sylow 2 G)
  (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
  (hkind : IsQuasisimple K ∨ Nat.card K = 3)
  (hKN : K ≤ normalizer (L : Set G))
  (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥)

include hL hLK hkind hKN hd

/-- The proved small symplectic ranks discharge the actual B.1.13 fixer premise. -/
theorem symplectic_smallRank_le_component {r f : ℕ} (hf : 0 < f)
    (hp : KnownSimple.SymplecticParameters r (2 ^ f)) (hr : r ≤ 2)
    (hmodel : ClassicalGroup.IsPSp (L ⧸ center L) r (2 ^ f)) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN (MulEquiv.refl _)
    (symplectic_smallRank_model_fixer hf hp hr hmodel) hd

/-- The odd orthogonal aliases discharge the same literal central-quotient premise. -/
theorem odd_smallRank_le_component {r f : ℕ} (hf : 0 < f)
    (hp : KnownSimple.OrthogonalOddParameters r (2 ^ f)) (hr : r ≤ 2)
    (hmodel : ClassicalGroup.IsPOmegaOdd (L ⧸ center L) r (2 ^ f)) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN (MulEquiv.refl _)
    (odd_smallRank_model_fixer hf hp hr hmodel) hd

/-- The minus-four family discharges the B.1.13 fixer premise, including q = 2. -/
theorem minusTwo_le_component {f : ℕ} (hf : 0 < f)
    (hmodel : ClassicalGroup.IsPOmegaMinus (L ⧸ center L) 2 (2 ^ f)) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN (MulEquiv.refl _)
    (minusTwo_model_fixer hf hmodel) hd

end Applications
end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar
