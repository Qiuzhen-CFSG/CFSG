module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter1.Defs
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.PResidual.Defs

/-!
# The general pushing-up setup

These are Hypothesis 4.1.1 and the collections on printed pp. 605–606 of
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004). All subgroups are embedded in the same ambient group. Products
are literal set products, relative normality is inside `M`, and `IsPPerfect 2`
expresses `M₊ = O²(M₊)`, not equality with its two-core.

The kernel of the action on `X/O₂(X)` is expressed by normalization of `X`
and the commutator bound modulo its characteristic two-core. The explicit
known-simple class parameter has the same meaning as in `Quasithin.Defs`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter4

open Subgroup
open scoped Pointwise

universe u
variable {G : Type u} [Group G]

/-- `C_G(X/O₂(X))`: normalizers acting trivially on the indicated section. -/
def sectionCentralizer (X : Subgroup G) : Subgroup G :=
  commutatorPreimage (normalizer (X : Set G)) X (X.pCoreIn 2)

/-- `C_A(X/O₂(X))`, including when `A` does not normalize all of `X`. -/
def sectionCentralizerIn (A X : Subgroup G) : Subgroup G :=
  A ⊓ sectionCentralizer X

/-- `M = !M(I)`: the maximal two-local overgroups of `I` form `{M}`. -/
def UniqueMaximalOvergroup (I M : Subgroup G) : Prop :=
  IsMaximalTwoLocal M ∧ I ≤ M ∧
    ∀ N : Subgroup G, IsMaximalTwoLocal N → I ≤ N → N = M

/-- The original hypotheses, with no pushing-up conclusions included. -/
structure Hypothesis411 [Finite G] (K : GroupClass.{u})
    (T : Sylow 2 G) (M Mplus : Subgroup G) : Prop where
  simpleQTKE : IsSimpleQTKE K G
  maximal : IsMaximalTwoLocal M
  sylow_le : (T : Subgroup G) ≤ M
  plus_le : Mplus ≤ M
  plus_normal : (Mplus.subgroupOf M).Normal
  plus_perfect : IsPPerfect 2 Mplus
  uniqueness : ∀ I : Subgroup G, I ≤ M →
    Mplus ⊔ sectionCentralizerIn (T : Subgroup G) Mplus ≤ I →
    (M : Set G) = (sectionCentralizerIn M Mplus : Set G) * (I : Set G) →
    UniqueMaximalOvergroup I M

/-- The collection `Σ(M₊)` (with its ambient subgroup `M` displayed). -/
def sigma (M Mplus : Subgroup G) : Set (Subgroup G) :=
  {Mminus | Mminus ≤ M ∧ Mplus ⊔ sectionCentralizerIn M Mplus ≤ Mminus}

/-- The covering subgroups `η(M₊,M₋)` on p. 606. -/
def eta (M Mplus Mminus : Subgroup G) : Set (Subgroup G) :=
  {I | I ≤ Mminus ∧
    (I : Set G) * (sectionCentralizerIn M Mplus : Set G) = (Mminus : Set G) ∧
    (Mplus : Set G) ⊆ (I : Set G) * (Mplus.pCoreIn 2 : Set G) ∧ I.pCoreIn 2 ≠ ⊥}

/-- The counterexamples: a covering subgroup with a nontrivial-core overgroup
outside `M`. `Chapter1.HOutside` is exactly the source's `H(I,M)`. -/
def mu (M Mplus Mminus : Subgroup G) : Set (Subgroup G) :=
  {I | I ∈ eta M Mplus Mminus ∧
    (Chapter1.HOutside G (I : Set G) (M : Set G)).Nonempty}

/-- The relation `I₁ ≲ I₂` compares both cores and intersections with `M₊`. -/
def PushLE (Mplus I₁ I₂ : Subgroup G) : Prop :=
  I₁.pCoreIn 2 ≤ I₂.pCoreIn 2 ∧ I₁ ⊓ Mplus ≤ I₂ ⊓ Mplus

/-- Maximal counterexamples. Maximality concerns strict growth of the core,
not maximality of the whole subgroup. -/
def muStar (M Mplus Mminus : Subgroup G) : Set (Subgroup G) :=
  {I | I ∈ mu M Mplus Mminus ∧
    ∀ I₁ ∈ mu M Mplus Mminus, PushLE Mplus I I₁ → ¬ I.pCoreIn 2 < I₁.pCoreIn 2}

end CFSG.Quasithin.Chapter4
