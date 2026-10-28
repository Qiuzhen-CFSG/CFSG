module
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# Cubic exchange with a source-specific midpoint core

The generic path exchange calculation only needs a subgroup `Q` containing the
correction terms and disjoint from both half-path radicals.  The older
`chosenApartmentExchange_of_cubic_pairs` wrapper hard-codes `Q` to the full
midpoint two-core. DGS (14.12) starts with that full core. In the natural-module
branch, (14.3)(b) and (14.9)(c) place the particular corrected reflection in
the smaller actor, so its discrepancy lies in the actor's own two-core.

This wrapper allows an arbitrary fixed core, but requires normalization by
every midpoint stabilizer. A smaller actor's own core need not satisfy that
stronger premise; `SmallActorExchange` provides the path-dependent consumer
using only normalization by the actual actor.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph
open Subgroup
open scoped Pointwise

variable {X V : Type*} [Group X] [MulAction X V]

-- Retain the two legacy named premises for callers of this public theorem.
set_option linter.unusedVariables false in
theorem chosenApartmentExchange_of_cubic_pairs_core
    {Γ : SimpleGraph V} (T : Set V)
    (n : ℕ) (K Q : Subgroup X)
    (hK : ∀ k∈K, ∀ z∈T, k • z=z)
    (hlocal : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=2*n →
      (∀ z∈p.support, z∈T) →
      (pathFixer (X := X) (p.drop n) : Set X) =
        (pathRoot (X := X) (p.drop n) : Set X) * (K : Set X))
    (hn : 0<n)
    (hQS : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=2*n →
      (∀ z∈p.support, z∈T) →
      pathRoot (X := X) (p.take n) ⊓ Q = ⊥)
    (hodd : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=n+1 →
      Odd (Nat.card (pathFixer (X := X) p)))
    (hQnorm : ∀ {v : V}, MulAction.stabilizer X v ≤
      Subgroup.normalizer (Q : Set X))
    (hpairs : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=2*n →
      (∀ z∈p.support, z∈T) → ∀ x∈pathRoot (X := X) (p.drop n), x≠1 →
      ∃ y∈pathRoot (X := X) (p.take n), ∃ t : X,
        x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
        (∀ k≤2*n, t • p.getVert k=p.getVert (2*n-k)) ∧
        (x*y*x)*t⁻¹∈Q ⊔ K)
    (hcentral : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=2*n →
      (∀ z∈p.support, z∈T) → ∀ x∈pathRoot (X := X) (p.drop n),
      ∀ y∈pathRoot (X := X) (p.take n), x*x=1 → y*y=1 → orderOf (x*y)=3 →
      ∀ h∈Q, Commute x h → Commute y h → h=1) :
    ChosenApartmentExchange (X := X) Γ T n := by
  intro a b p hp hl hT g hg hmove
  have hfix : K ≤ pathFixer (X := X) p := by
    intro k hk j _
    exact hK k hk _ (hT _ (p.getVert_mem_support j))
  rcases halfFixer_exchange_or_centralizer p n hl K Q hfix
      (hlocal p hp hl hT) (hQS p hp hl hT) (hQnorm (v := p.getVert n))
      (hpairs p hp hl hT)
      g hg hmove with he | ⟨x,hx,y,hy,hxx,hyy,hc,z,hz,hzne,hxz,hyz⟩
  · exact he
  · exact (hzne (hcentral p hp hl hT x hx y hy hxx hyy hc z hz hxz hyz)).elim

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
