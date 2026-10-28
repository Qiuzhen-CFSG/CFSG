module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.FinalParagraph
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.QuotientTransport

/-!
# Assembly of the mixed-involution centralizer argument

The rank and nonnesting reductions feed source (d) in a proper centralizer.
The central case is the remaining quotient exclusion. The two exclusions
and the earlier local-control theorem remain explicit inputs here; their
producers must discharge them before the minimal-counterexample form of (g)
is complete. The final theorem applies this bound to the already proved
product-fusion paragraph.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J.
Math. 19 (1975), Lemma 3.4(g), pp.95–96, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G]
variable {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Assemble (g) from the earlier local induction and the two remaining exclusions. -/
theorem Hypotheses.productCentralizers_of_localControl_of_exclusions
    (h : Hypotheses S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    (hl : LocalControl S A₁ A₂)
    (hm : MixedCentralizerModelExclusion A₁ A₂)
    (hq : MixedCentralQuotientExclusion A₁ A₂) : ProductCentralizerInput A₁ A₂ := by
  intro a ha b hb ha2 hb2 hab
  by_contra hK
  have hproper : centralizer ({a * b} : Set G) ≠ ⊤ := by
    intro he
    apply hq a ha b hb ha2 hb2 hab
    apply mem_center_iff.mpr
    intro x
    apply mem_centralizer_singleton_iff.mp
    rw [he]
    exact mem_top x
  have hr := h.mixed_centralizer_ranks ha hb ha2 hb2
  have hn := h.mixed_centralizer_nonnesting hc ha hb hab hK
  have hu : a * b ∈ A₁ ⊔ A₂ :=
    (A₁ ⊔ A₂).mul_mem ((show A₁ ≤ A₁ ⊔ A₂ from le_sup_left) ha)
      ((show A₂ ≤ A₁ ⊔ A₂ from le_sup_right) hb)
  exact (hl.centralizers (a * b) hu (h.mixed_orderOf ha hb ha2 hb2 hab)
    hr.1 hr.2 hn.1 hn.2 (hm a ha b hb ha2 hb2 hab hproper hK)).elim hproper hK

/-- The conditional centralizer bound feeds the literal product-fusion consumer.
All three earlier-source inputs remain explicit. -/
theorem MinimalCounterexample.fusionConclusion_of_mixedCentralizer_exclusions
    (m : MinimalCounterexample S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    (hl : LocalControl S A₁ A₂)
    (hm : MixedCentralizerModelExclusion A₁ A₂)
    (hq : MixedCentralQuotientExclusion A₁ A₂) : FusionConclusion S A₁ A₂ :=
  m.setup.fusionConclusion_of_closed_of_productCentralizers hc
    (m.setup.productCentralizers_of_localControl_of_exclusions hc hl hm hq)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
