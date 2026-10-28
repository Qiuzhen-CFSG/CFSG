module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.ProductGeometry
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Selection

/-!
# Assembling the component reductions B.5.9–10

The preliminary classification is supplied for every moved component. In its
natural branch, the second-component and chief-factor argument proves the
literal equality U=[C_V(O₂(LA)),L]=[V,L]. Restricting the ambient moved-space
action to LA identifies the two subrepresentations and transports the natural
action, including its group identification and intertwiner. This closes the
five alternatives of B.5.9 without assuming any dimension or multiplicity bound.

Selection constructs a minimal best offender and a normal component L=[L,A].
Applying the five-case result and the proved product geometry then constructs
`Conclusion`: G₁=L (or LA in the marked S₅ case), V₁=[V,L], V₂=C_V(G₁),
G₂=C_G(G₁), the multiplication-compatible internal product, G₂=C_G(V₁), and
the supplement or exceptional natural-SL₃(2) hyperplane alternative. Its
`descent` application supplies B.5.3 and strict order descent on the literal
complementary factor and fixed subspace.

Exactly four universal earlier-source implications remain explicit:
* `ProjectiveLine.QuasisimpleClassificationInput`: all six B.5.1 clauses with
  the corrected projective-line convention; producer `qt-b05-quasisimple`;
* `PreliminaryActions.Preparation.ComponentInput`: B.5.5 on the original
  B.5.3 action; producer `qt-b05-quotient-components`;
* `PreliminaryActions.ThreeCovers.CentralExtension.EarlierB48Two`: B.4.8(2),
  retaining the specified natural central quotient and all offender, ratio,
  Sylow-fixed and involution conclusions; producers
  `qt-b-04-natural-extensions` / `qt-b-04`;
* universal `ChapterA.Section02.TheoremA`: all of A.2.1, applied to the actual
  SQTK cover in the second-component argument; producer `qt-a-02`.

Their final discharge belongs to `qt-b05-general-classification`. The two
intermediate premises, that all minimal best offenders centralize F(G) and
that all components have three-rank one, remain with the parent's B.5.8 and
high-three-rank reductions. No counterexample hypothesis is needed after
these premises have been supplied. Neither the preliminary classification,
natural closure, B.5.9 action alternatives nor B.5.10 geometry is assumed.
This proves the requested conditional component reduction, not the full B.5.6
classification or any of those earlier universal implications.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9–10 and the selection preceding them, printed pp.106–109.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

omit [Finite G] in
/-- Transport the actual natural action along U=[V,L]. Only restriction to
LA is used in identifying the seed with the ambient moved subrepresentation. -/
theorem NaturalSeed.componentActionCase {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) (s : MovedSection ρ L)
    (he : seed.space.toSubmodule = moved ρ L) :
    ComponentActionCase ρ A L s L := by
  let W : Subrepresentation (ρ.comp (L ⊔ A).subtype) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule g hv⟩
  have hW : seed.space = W := Subrepresentation.ext (he.trans s.space_eq.symm)
  have hn := seed.natural
  rw [hW] at hn
  exact .naturalThree seed.field seed.odd_degree ⟨hn⟩ seed.inner

/-- B.5.9 for every component L=[L,A], on any literal moved section. The
universal preliminary classification and the natural closure are proved
from the source setup and the four stated earlier implications. -/
theorem componentActionCase_of_source
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h48 : PreliminaryActions.ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    (theoremA : ∀ (D : Type u) [Group D] [Finite D], ChapterA.Section02.TheoremA K D)
    (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hAF : A ≤ centralizer (fittingSubgroup G : Set G))
    (h3 : ∀ M, IsComponent G M → primeRank 3 M = 1)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L) :
    ∃ H, ComponentActionCase ρ A L s H := by
  have setup := PreliminaryActions.naturalClosureSetup_of_source ρ h5 h1 h48 hyp hA hAF h3
  cases setup.preliminary L hL hLA s with
  | classified H hc => exact ⟨H, hc⟩
  | naturalSeed seed =>
    exact ⟨L, seed.componentActionCase ρ s
      (NaturalClosure.seed_eq_moved ρ setup theoremA hL hLA seed)⟩

/-- Select the actual minimal offender and moved component, establish all
five B.5.9 alternatives, and construct all three B.5.10 conclusions. The
parent supplies B.5.8 centralization and the three-rank-one reduction. -/
theorem conclusion_of_source [Nontrivial G]
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h48 : PreliminaryActions.ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    (theoremA : ∀ (D : Type u) [Group D] [Finite D], ChapterA.Section02.TheoremA K D)
    (hyp : FFHypothesis K ρ)
    (hfit : ∀ A, IsMinimalBestOffender ρ A →
      A ≤ centralizer (fittingSubgroup G : Set G))
    (h3 : ∀ M, IsComponent G M → primeRank 3 M = 1) :
    Nonempty (Conclusion ρ) := by
  obtain ⟨A, L, hA, hL, hnL, hLA, _⟩ :=
    select_component ρ hyp hfit (h5 G V ρ hyp).normal
  let : L.Normal := hnL
  let s := MovedSection.ofNormal ρ L
  obtain ⟨H, hc⟩ := componentActionCase_of_source ρ h5 h1 h48 theoremA hyp
    hA (hfit A hA) h3 hL hLA s
  exact ProductGeometry.conclusion_of_componentActionCase hyp hA hL hLA s hc

omit [Finite G] in
/-- The first factor is L in four cases and LA in the marked S₅ case. -/
theorem ComponentActionCase.component_le_first {A L H : Subgroup G}
    {s : MovedSection ρ L} (hc : ComponentActionCase ρ A L s H) : L ≤ H := by
  cases hc <;> first | exact le_rfl | exact le_sup_left

omit [Finite G] in
/-- The selected component witnesses nontriviality of the first factor. -/
theorem Conclusion.first_ne_bot (c : Conclusion ρ) : c.first ≠ ⊥ := by
  let : IsSimpleGroup (c.component ⧸ center c.component) := c.isComponent.2.simple
  let : Nontrivial c.component := (QuotientGroup.mk'_surjective (center c.component)).nontrivial
  have hn : c.component ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  intro he
  apply hn
  apply bot_unique
  simpa only [he] using c.actionCase.component_le_first ρ

/-- The B.5.11 descent consumer on G₂=C_G(G₁) and V₂=C_V(G₁). All B.5.3
hypotheses and strict descent follow from the constructed component reduction;
no further faithfulness, generation or nontriviality premise is required. -/
theorem Conclusion.descent (c : Conclusion ρ) (hyp : FFHypothesis K ρ) :
    Nat.card (centralizer (c.first : Set G)) < Nat.card G ∧
      FFHypothesis K (c.productConfiguration.fixed.toRepresentation.comp
        (centralizer (c.first : Set G)).subtype) :=
  c.productConfiguration.descent ρ hyp (c.first_ne_bot ρ)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
