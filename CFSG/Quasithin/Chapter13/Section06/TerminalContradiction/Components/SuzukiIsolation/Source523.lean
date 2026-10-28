module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Definitions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.ChapterA.Section04.Defs
public import CFSG.Quasithin.Chapter3.Defs
public import CFSG.Quasithin.ChapterE.Defs
public import CFSG.Quasithin.ClassificationModels.RankTwo
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.MaximalTwoLocalOvergroups
public import Theory.Representation.BinaryPermutation
public import Stellmacher.SectionsOneToFourDefs

/-!
# The full earlier 5.2.3 implication

This is a statement of the earlier theorem, supplied explicitly to the
13.6.27 argument, not a proof of 5.2.3. Its producer is `qt-5-03`.

The antecedent retains the genuine maximal faithful local component,
relative normality in a maximal two-local, the reduced elementary module,
and its nontrivial conjugation action. The conclusion retains all three
source alternatives. In particular, the exceptional local alternative
includes the equivariant sum of at most two orthogonal A₅ modules and a
C-component of the literal C_G(Ω₁(Z(T))), with the actual residual embedding.
The global alternatives are M₂₃ and the complete rank-two family, including
the small derived groups and the restriction U₅(q) only for q = 4.

The A₅ module is the even-weight subspace on five letters. Since five is
odd, this is the usual natural alternating-five module, not the natural
two-dimensional SL₂(4) module. An injective homomorphism onto V with the
displayed conjugation identities gives actual module coordinates; no family
tag or arbitrary proposition stands for the module clause.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Theorem 5.2.3,
printed p.649 / PDF p.666; module convention §B.3 and source R₂ in B.2.11.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Source523

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Equivariant coordinates for a sum of at most two copies of the
orthogonal A₅ module, with the action through the actual two-core quotient. -/
def A5ModuleSum (L V : Subgroup G) : Prop :=
  ∃ c : ℕ, c ≤ 2 ∧
    ∃ e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5),
    ∃ f : Multiplicative (Fin c → BinaryPermutation.core (Fin 5)) →* G,
      Function.Injective f ∧ f.range = V ∧
      ∀ (l : L) (v : Fin c → BinaryPermutation.core (Fin 5)),
        MulAut.conj (l : G) (f (Multiplicative.ofAdd v)) =
          f (Multiplicative.ofAdd (fun i =>
            BinaryPermutation.coreRepresentation (Fin 5)
              (e (QuotientGroup.mk' (pCore 2 L) l)).val (v i)))

/-- The source hypotheses independent of the chosen HStar member.
Normality is relative to M; the module lies in LT and is reduced there. -/
structure Setup (κ : GroupClass.{u}) (T : Sylow 2 G)
    (L M V : Subgroup G) (n : ℕ) : Prop where
  qtke : IsSimpleQTKE κ G
  maximal_local : L ∈ Chapter1.LStar G (T : Subgroup G)
  faithful : ChapterA.Section04.IsFaithfulSignalizerType L
  linear : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)
  contains : L ≤ M
  normal : (L.subgroupOf M).Normal
  maximal_two_local : M ∈ maximalTwoLocalOvergroups (T : Subgroup G)
  module_le : V ≤ L ⊔ (T : Subgroup G)
  reduced : Theory.GroupTheory.IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G)))
  noncentral : ⁅V, L⁆ ≠ ⊥

/-- All clauses of the exceptional local alternative in 5.2.3(1).
The residual and component are compared only after their actual embeddings
into G; no ambient normality is imposed on the centralizer component. -/
def LocalAlternative (T : Sylow 2 G) (L H V : Subgroup G) (n : ℕ) : Prop :=
  n = 2 ∧ A5ModuleSum L V ∧
    ∃ KZ : Subgroup (centralizer (Stellmacher.omegaOneCenterAmbient
        (T : Subgroup G) : Set G)),
      KZ.IsCComponent ∧
      (pResidual 2 H).map H.subtype ≤ KZ.map
        (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype ∧
      ((ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
          (Nonempty ((KZ ⧸ pCore 2 KZ) ≃* alternatingGroup (Fin 7)) ∨
           Nonempty ((KZ ⧸ pCore 2 KZ) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
           Nonempty ((KZ ⧸ pCore 2 KZ) ≃* Sporadic.Mathieu.M23))) ∨
        ((pResidual 2 H).map H.subtype = KZ.map
            (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype ∧
          Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four)))

/-- The complete global alternatives, retaining the actual model isomorphisms. -/
def GlobalAlternative (G : Type u) [Group G] : Prop :=
  Nonempty (G ≃* Sporadic.Mathieu.M23) ∨ ∃ f : ℕ, ClassificationModels.IsRankTwoModel G f

/-- The complete universal earlier theorem, over all finite ambient groups
in the fixed source class κ. Final source assembly uses the full known-simple
class, and must discharge this assumption using the Chapter 5 producer. -/
def EarlierTheorem (κ : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X)
    (L M V : Subgroup X) (n : ℕ), Setup κ T L M V n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup X) M, 1 < ChapterE.generationParameter H →
      LocalAlternative T L H V n ∨ GlobalAlternative X

/-- Keep the full earlier theorem as input while extracting just its
residual-model consequence, or one of its unexcluded global alternatives. -/
theorem residual_models_or_global {κ : GroupClass.{u}}
    (h523 : EarlierTheorem κ) {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
    (h : Setup κ T L M V n) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < ChapterE.generationParameter H) :
    (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∨
      Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four)) ∨
      GlobalAlternative G := by
  rcases h523 G T L M V n h H hH hn with hlocal | hglobal
  · obtain ⟨_, _, KZ, _, _, hKZ⟩ := hlocal
    exact Or.inl (hKZ.elim (fun hK => Or.inl hK.1) (fun hK => Or.inr hK.2))
  · exact Or.inr hglobal

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Source523
