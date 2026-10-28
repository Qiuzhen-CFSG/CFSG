module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.QuasisimpleBranch
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentReduction

/-!
# Separating the two genuine component branches of F.6.17

The source component reduction constructs and orients K from the original
SQTK quotient. If it contains both local residuals, the quasisimple
conclusion is proved. Otherwise the selected component contains exactly
one residual, and the opposite original two-core is Sylow in its normal
product with K. All witness fields are constructed here.

This is the actual input for the remaining rigidity and component-model
argument in F.6.17(2); it asserts no model recognition. Theorem A on the
original SQTK cover retains its existing independent source producer.
Source: Aschbacher--Smith F.6.17, printed p.309 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual oriented component and normal-product Sylow data after
excluding the proved quasisimple-residual alternative. -/
structure SingleResidualComponent (G₁ G₂ : Subgroup G) where
  component : Subgroup G
  isComponent : IsComponent G component
  normal : component.Normal
  left_contains : (pResidual 2 G₁).map G₁.subtype ≤ component
  right_escapes : ¬ (pResidual 2 G₂).map G₂.subtype ≤ component
  generates : component ⊔ G₂ = ⊤
  core_join_normal : (component ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G).Normal
  core_sylow : ∃ S : Sylow 2 (component ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G),
    (S : Subgroup (component ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G)).map
      (component ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G).subtype =
      (pCore 2 G₂).map G₂.subtype

private theorem singleResidualComponent_of_source
    {G₁ G₂ : Subgroup G} (h : IsGoldschmidtTriple G₁ G₂)
    (K : Subgroup G) (hK : IsComponent G K) [K.Normal]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ K)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ K) :
    Nonempty (SingleResidualComponent G₁ G₂) := by
  obtain ⟨hg, hn, hs⟩ := normal_subgroup_rigidity_setup h K h₁ h₂
  exact ⟨⟨K, hK, inferInstance, h₁, h₂, hg, hn, hs⟩⟩

variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
variable {G₁ G₂ : Subgroup G}

/-- The original cyclic-three-core quotient either satisfies F.6.17(1),
or has the precise single-residual component used in the remaining branch.
Component existence, normality, orientation and Sylow setup are all discharged. -/
theorem source_F_6_17_reduction
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    (hc : IsCyclic (pCore 3 G)) :
    (pResidual 2 G = generalizedFitting G ∧ IsQuasisimple (pResidual 2 G)) ∨
      Nonempty (SingleResidualComponent G₁ G₂) ∨
      Nonempty (SingleResidualComponent G₂ G₁) := by
  obtain ⟨K, hK, hn, _, horient⟩ := cyclic_component_reduction hA hH e h hc
  let : K.Normal := hn
  rcases horient with ⟨h₁, _⟩ | ⟨h₂, _⟩
  · by_cases h₂ : (pResidual 2 G₂).map G₂.subtype ≤ K
    · exact Or.inl (source_F_6_17_quasisimple_branch e h K hK h₁ h₂)
    · exact Or.inr (Or.inl (singleResidualComponent_of_source h K hK h₁ h₂))
  · by_cases h₁ : (pResidual 2 G₁).map G₁.subtype ≤ K
    · exact Or.inl (source_F_6_17_quasisimple_branch e h K hK h₁ h₂)
    · exact Or.inr (Or.inr (singleResidualComponent_of_source h.symm K hK h₂ h₁))

/-- The exceptional-left source case constructs the elementary Sylow
input on the same component chosen by the original reduction. -/
theorem SingleResidualComponent.small_sylow_of_exceptional_left
    (d : SingleResidualComponent G₁ G₂)
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁) :
    Nonempty (((pResidual 2 G₁).map G₁.subtype) ≃* Multiplicative (ZMod 3)) ∧
      IsElementaryAbelian 2 ((pCore 2 G₂).map G₂.subtype) ∧
      primeRank 2 ((pCore 2 G₂).map G₂.subtype) ≤ 3 ∧
      IsSimpleGroup (d.component ⧸ center d.component) ∧
      ∃ S : Sylow 2 (d.component ⧸ center d.component),
        IsElementaryAbelian 2 S ∧ Nat.card S ≤ 8 := by
  let : d.component.Normal := d.normal
  obtain ⟨_, _, _, hc, he, hr, hs, S, hS, hcard⟩ :=
    component_rigidity_of_exceptional_left h hcore hbad d.component d.isComponent
      d.left_contains d.right_escapes
  exact ⟨hc, he, hr, hs, S, hS, hcard⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
