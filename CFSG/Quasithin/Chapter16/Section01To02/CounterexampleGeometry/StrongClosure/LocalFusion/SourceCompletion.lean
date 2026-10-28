module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.LocalFusion
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.Induction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalGeometry.NestedPermutation
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalGeometry.CentralizerReselection
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.ModelExclusion
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.CentralQuotient

/-!
# Complete local fusion for Aschbacher's Lemma 3.4

Nested factors give global strong closure directly, and each mixed product
belongs to the larger factor. For incomparable factors, pair permutation and
Sylow reselection supply local control. Contrary involution fusion then gives
global strong closure; the proper-centralizer model argument and the central
quotient exclusion supply (g) and the final product-fusion paragraph.

Thus every minimal counterexample satisfies the full `FusionConclusion`,
without additional closure, local-control or exclusion premises. Its product
unique-conjugate membership also recovers the centralizer bound in both
nesting orientations. The induction consumer below discharges the local-fusion
premise, retaining only the exact ZD theorem and its universal terminal
implication. Those are separate obligations for the full Lemma 3.4.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4(a)--(g) and the final product paragraph, printed pp.94--96,
DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory

universe u
variable {G : Type u} [Group G] [Finite G]
variable {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Source (b)--(d) for incomparable factors, including actual Sylow reselection
and both relative-factor exclusions in the centralizer induction. -/
theorem MinimalCounterexample.localControl_of_nonnested
    (m : MinimalCounterexample S A₁ A₂) (hn₁ : ¬ A₁ ≤ A₂) (hn₂ : ¬ A₂ ≤ A₁) :
    LocalControl S A₁ A₂ := by
  have hp := m.setup.permutes_pair_of_nonnested hn₁ hn₂
  exact ⟨hp, m.setup.unique_large, m.centralizer_alternative_after_reselection hp⟩

/-- The entire local-fusion argument of Lemma 3.4 in an arbitrary minimal
counterexample. The nested branch uses the larger factor directly; the
incomparable branch discharges every local-control and exclusion premise. -/
theorem MinimalCounterexample.fusionConclusion
    (m : MinimalCounterexample S A₁ A₂) : FusionConclusion S A₁ A₂ := by
  by_cases hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁
  · exact m.setup.fusionConclusion_of_nested hn
  · have hl := m.localControl_of_nonnested
      (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))
    have hc := m.setup.closed_of_involution_transporters
      (m.involution_transporters_of_localControl hl)
    exact m.fusionConclusion_of_mixedCentralizer_exclusions hc hl
      (m.mixedCentralizerModelExclusion_of_closed hc hl)
      (m.mixed_central_quotient_exclusion hc hl)

/-- Source (e), with no nesting restriction or additional local input. -/
theorem MinimalCounterexample.closed
    (m : MinimalCounterexample S A₁ A₂) :
    IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤ :=
  m.fusionConclusion.closed

/-- The final product-fusion paragraph, for every nonidentity product of
involutions from the two factors, including nested factors. -/
theorem MinimalCounterexample.productFusion
    (m : MinimalCounterexample S A₁ A₂) : ProductFusionInput A₁ A₂ :=
  m.fusionConclusion.product_unique

/-- Source (g) in both the nested and incomparable cases. Unique conjugate
membership, already proved above, forces the actual mixed centralizer into H. -/
theorem MinimalCounterexample.productCentralizers
    (m : MinimalCounterexample S A₁ A₂) : ProductCentralizerInput A₁ A₂ := by
  intro a₁ ha₁ a₂ ha₂ ha₁order ha₂order hne
  exact (m.fusionConclusion.product_unique a₁ ha₁ a₂ ha₂ ha₁order ha₂order hne).centralizer_le

/-- The literal strong-induction consumer with local fusion fully discharged.
Only ZD and its existing terminal implication remain to prove the full source
alternatives, including strong embedding in the first factor's normal closure. -/
theorem conclusion_of_terminal
    (zd : TheoremZD.{u})
    (terminal : TheoremZD.{u} →
      ∀ {X : Type u} [Group X] [Finite X]
        (P : Sylow 2 X) (B₁ B₂ : Subgroup X),
        Hypotheses P B₁ B₂ → FusionConclusion P B₁ B₂ → Conclusion B₁ B₂)
    (S : Sylow 2 G) (A₁ A₂ : Subgroup G) (h : Hypotheses S A₁ A₂) :
    Conclusion A₁ A₂ :=
  conclusion_of_fusion_and_terminal zd (fun _ _ _ m => m.fusionConclusion)
    terminal S A₁ A₂ h

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
