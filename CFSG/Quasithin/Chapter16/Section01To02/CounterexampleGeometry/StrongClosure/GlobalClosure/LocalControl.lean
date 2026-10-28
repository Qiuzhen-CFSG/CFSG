module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.LocalFusion.Basic

/-!
# The local geometry preceding global strong closure

This record specifies source (b)--(d) of Aschbacher's Lemma 3.4. It is a
contract for the local-geometry producer, not a theorem asserting these
properties. A separate contrary-fusion proof may take this contract explicitly;
the global-closure assembly must construct it from `MinimalCounterexample`.

The centralizer factors are `Aᵢ.subgroupOf C_G(u)`, so their elements are the
actual intersections with the centralizer. Conjugacy and both model alternatives
are tested inside that same centralizer. Only conjugacy there is needed to
exclude the exceptional alternative in the induction hypothesis. The two
nonnesting conditions compare the ambient intersections with the other factor.
No global strong closure or product-fusion assertion is included.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4, printed pp.94--95, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1

universe u

/-- The source assertions (b), (c), and the induction alternative (d), kept
separate from the global-closure conclusion (e). -/
structure LocalControl {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (A₁ A₂ : Subgroup G) : Prop where
  permutes_pair : ∀ s ∈ S,
    (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
    (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁)
  unique_large : ∀ X : Subgroup G, (X ≤ A₁ ∨ X ≤ A₂) → 2 < Nat.card X →
    UniqueSubgroupConjugateMembership (intersectionGenerated A₁ A₂) X
  centralizers : ∀ u ∈ A₁ ⊔ A₂, orderOf u = 2 →
    let K := centralizer ({u} : Set G)
    TwoRankAtLeastTwo (A₁.subgroupOf K) →
    TwoRankAtLeastTwo (A₂.subgroupOf K) →
    (¬ A₁ ⊓ K ≤ A₂) → (¬ A₂ ⊓ K ≤ A₁) →
    (∀ g : K, conjugate (A₁.subgroupOf K) g = A₂.subgroupOf K →
      ¬ DihedralOrSemidihedral (A₁.subgroupOf K)) →
    K = ⊤ ∨ K ≤ intersectionGenerated A₁ A₂

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
