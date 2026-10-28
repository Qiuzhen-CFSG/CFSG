module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.Restriction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalGeometry.PairGeometry
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalGeometry.CentralizerReselection.Selection
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalGeometry.CentralizerReselection.ExceptionalTransport

/-!
# Reselection for the centralizer induction in Aschbacher 3.4(d)

`Selection` proves the actual restricted Sylow equality after conjugation
inside H, retains both relative factors and their rank and nonnesting clauses,
and applies induction once the exceptional alternative for the new pair is
excluded. `ExceptionalTransport` excludes that alternative using the original
relative factors and their concrete model exclusion. Together these prove
`MinimalCounterexample.centralizer_alternative_after_reselection`, with no
Sylow-placement premise. Pair permutation remains the explicit source (b)
input supplied by the parent local-geometry assembly.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4(d), printed p.95, DOI 10.1215/ijm/1256050927.
-/

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1

universe u
variable {G : Type u} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Source (d) after the permitted Sylow reselection inside H. Both original
relative centralizers, their rank and nonnesting conditions, and the actual
dihedral/semidihedral exclusion suffice; no local Sylow placement is assumed. -/
public theorem MinimalCounterexample.centralizer_alternative_after_reselection
    (m : MinimalCounterexample S A₁ A₂)
    (hperm : ∀ s ∈ S,
      (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁))
    (u : G) (hu : u ∈ A₁ ⊔ A₂) (hou : orderOf u = 2)
    (hr₁ : TwoRankAtLeastTwo (A₁.subgroupOf (centralizer ({u} : Set G))))
    (hr₂ : TwoRankAtLeastTwo (A₂.subgroupOf (centralizer ({u} : Set G))))
    (hn₁ : ¬ A₁ ⊓ centralizer ({u} : Set G) ≤ A₂)
    (hn₂ : ¬ A₂ ⊓ centralizer ({u} : Set G) ≤ A₁)
    (hmodel : ∀ g : centralizer ({u} : Set G),
      conjugate (A₁.subgroupOf (centralizer ({u} : Set G))) g =
        A₂.subgroupOf (centralizer ({u} : Set G)) →
      ¬ DihedralOrSemidihedral (A₁.subgroupOf (centralizer ({u} : Set G)))) :
    centralizer ({u} : Set G) = ⊤ ∨
      centralizer ({u} : Set G) ≤ intersectionGenerated A₁ A₂ :=
  m.centralizer_alternative_of_reselection_model_exclusion hperm u hu hou hr₁ hr₂ hn₁ hn₂ hmodel

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
