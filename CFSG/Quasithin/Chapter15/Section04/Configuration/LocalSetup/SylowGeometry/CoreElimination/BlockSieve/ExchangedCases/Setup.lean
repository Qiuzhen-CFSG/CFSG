module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.SourceComparison
public import CFSG.Quasithin.ChapterC.Defs
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Selected factors and genuine component inputs for the exchanged sieve

A selected witness retains the original factor, conjugating element, join and
setwise product. Its relative subnormality gives the actual embedding of its
core quotient into H/O₂(H). No normality in the ambient group is asserted.

`ComponentHypotheses` records all the hypotheses of C.2.3 and C.2.7,
uniformly in the ambient group. The local radical assertion of C.2.2(3) is a
consequence still to be proved, not an added field. `SelectedConclusion` is
the terminal contract, retaining both the L₂ block and alternating-five block.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.2.3 and
C.2.7, printed pp.144–147; 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
universe u
variable {G : Type u} [Group G]

/-- A selected witness to the exchanged embedding, with the literal product. -/
structure Selected (H U K K₁ : Subgroup G) (r : G) : Prop where
  component : K₁ ∈ Chapter1.cComponentsIn H
  conjugator_mem : r ∈ U
  conjugator_moves : r ∉ normalizer (K₁ : Set G)
  join_eq : K₁ ⊔ K₁.map (MulAut.conj r).toMonoidHom = K
  product_eq : (K : Set G) = (K₁ : Set G) * (K₁.map (MulAut.conj r).toMonoidHom : Set G)
  model : Chapter1.XiEmbedding.SwappedModel 3 (K₁ ⧸ pCore 2 K₁)

theorem exists_selected {H U K : Subgroup G} (h : ExchangedEmbedding H U K) :
    ∃ K₁ r, Selected H U K K₁ r := by
  obtain ⟨K₁, r, hc, hr, hn, hj, hp, hm⟩ := h
  exact ⟨K₁, r, hc, hr, hn, hj, hp, hm⟩

/-- The complete genuine hypotheses preceding C.2.7(1)–(3), uniformly in A.
This contains no classification or local-radical conclusion. -/
structure ComponentHypotheses (κ : GroupClass.{u}) (A : Type u) [Group A]
    (R M L : Subgroup A) : Prop where
  sqtk : IsSQTK κ A
  radical : ChapterC.IsTwoRadical R
  characteristic_control : ChapterC.characteristicNormalizer R ≤ M
  sylow_closure : ChapterC.IsSylowInNormalClosure R M
  component : L.IsCComponent
  quasisimple : IsQuasisimple (L ⧸ pCore 2 L)
  characteristic_two : generalizedFitting L = pCore 2 L
  outside : ¬ L ≤ M
  normalized : R ≤ normalizer (L : Set A)

/-- The unreduced terminal target for the same selected component and conjugator. -/
def SelectedConclusion (H U K K₁ : Subgroup G) (r : G) : Prop :=
  Selected H U K K₁ r ∧ (K₁.subgroupOf H).IsSubnormal ∧
    ((∃ n, Even n ∧ Nat.ModEq 3 (2 ^ n) 1 ∧ ChapterC.IsL2EvenBlock K₁ n) ∨
      ChapterC.IsAlternatingBlock K₁ 5)

variable {H U K K₁ : Subgroup G} {r : G}

theorem Selected.relative_subnormal (s : Selected H U K K₁ r) :
    (K₁.subgroupOf H).IsSubnormal := s.component.2.subnormal

/-- The selected factor quotient identifies with its intrinsic realization in H. -/
noncomputable def Selected.internalQuotientEquiv (s : Selected H U K K₁ r) :
    (K₁ ⧸ pCore 2 K₁) ≃*
      ((K₁.subgroupOf H) ⧸ pCore 2 (K₁.subgroupOf H)) := by
  let e := (subgroupOfEquivOfLe s.component.1).symm
  exact QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

/-- The same selected quotient embeds as its actual image in H/O₂(H). -/
noncomputable def Selected.factorQuotientEmbedding [Finite G]
    (s : Selected H U K K₁ r) : (K₁ ⧸ pCore 2 K₁) →* (H ⧸ pCore 2 H) :=
  ((K₁.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype.comp
    ((cComponentTwoCoreQuotientEquiv s.component.2).toMonoidHom.comp
      s.internalQuotientEquiv.toMonoidHom)

theorem Selected.factorQuotientEmbedding_injective [Finite G]
    (s : Selected H U K K₁ r) : Function.Injective s.factorQuotientEmbedding :=
  Subtype.val_injective.comp ((cComponentTwoCoreQuotientEquiv s.component.2).injective.comp
    s.internalQuotientEquiv.injective)


/-- Representatives map to the same ambient element, not merely to an abstract copy. -/
theorem Selected.factorQuotientEmbedding_apply [Finite G]
    (s : Selected H U K K₁ r) (g : K₁) :
    s.factorQuotientEmbedding (QuotientGroup.mk' (pCore 2 K₁) g) =
      QuotientGroup.mk' (pCore 2 H) ⟨g, s.component.1 g.property⟩ := rfl

/-- C.2.7's normalization premise makes L normal in LR, intrinsically. -/
theorem ComponentHypotheses.local_normal {κ : GroupClass.{u}}
    {R M L : Subgroup G} (h : ComponentHypotheses κ G R M L) :
    (L.subgroupOf (L ⊔ R)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer h.normalized)

/-- The component core is its intersection with the local core. -/
theorem ComponentHypotheses.local_component_core [Finite G] {κ : GroupClass.{u}}
    {R M L : Subgroup G} (h : ComponentHypotheses κ G R M L) :
    pCore 2 (L.subgroupOf (L ⊔ R)) =
      (pCore 2 (L ⊔ R : Subgroup G)).comap (L.subgroupOf (L ⊔ R)).subtype :=
  pCore_subnormal_eq_comap 2 h.local_normal.isSubnormal
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
