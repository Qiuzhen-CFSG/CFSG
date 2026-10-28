module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.ModelExclusion.Recognition
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.ModelExclusion.FullFactorGeometry

/-!
# The remaining full-factor branch in the mixed centralizer exclusion

The four-group and nonabelian centralizer calculations recognize both ambient
factors as actual dihedral or semidihedral groups. Thus the requested local
model exclusion follows from the proper mixed-centralizer bound in that
full-factor case. That bound remains an explicit source obligation here.
In particular, recognition alone supplies neither the fused conjugator nor
the order-two intersection required by the original `Exceptional` alternative.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J.
Math. 19 (1975), Lemma 3.4(g), bottom of p.95 and top of p.96,
DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G]
variable {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Recognition reduces the mixed-centralizer model exclusion to its full-factor
source branch. The bound must still be constructed from minimality and local control. -/
theorem Hypotheses.mixedCentralizerModelExclusion_of_factor_bound
    (h : Hypotheses S A₁ A₂) (hf : ModelFactorMixedCentralizerBound A₁ A₂) :
    MixedCentralizerModelExclusion A₁ A₂ := by
  intro a ha b hb ha2 hb2 hab K hproper hK g hg hm
  obtain ⟨hm₁, hm₂⟩ := h.factor_models_of_conjugate_mixed_centralizers ha hb ha2 hb2 g hg hm
  exact hK (hf hm₁ hm₂ a ha b hb ha2 hb2 hab hproper g hg)

/-- The mixed-centralizer model branch follows from the full-factor source
branch proved by minimality inside each proper mixed centralizer. -/
theorem MinimalCounterexample.mixedCentralizerModelExclusion_of_closed
    (m : MinimalCounterexample S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    (hl : LocalControl S A₁ A₂) : MixedCentralizerModelExclusion A₁ A₂ := by
  exact m.setup.mixedCentralizerModelExclusion_of_factor_bound
    (m.modelFactorMixedCentralizerBound_of_closed hc hl)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
