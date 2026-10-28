module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors.Context
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.Paired
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors.TensorModels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors.CentralizingRank
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors.InvolutionDisplacement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors.NormalThree

/-!
# Quantitative outer-actor calculations for the linear-three alternatives

The tensor branch is proved in `OuterActors.TensorModels`, including faithful
concrete models, exact outer fixed codimensions, component actors, and transport.
For the paired branch, actors centralizing X have rank at most two and contain
an outer involution displacing at least six dimensions. Actors not centralizing
X have rank one and displace half the module, whose dimension is at least twelve.
Thus every outer quadratic actor has fixed codimension strictly greater than
twice its rank. The proof preserves the actual H, K and X of
`OuterActors.PairedSetup`, including the conjugation kernel, throughout.

Source: Aschbacher–Smith 13.8.21(1), printed pp.956–957, combined manuscript
of 1 March 2004. Final chief-factor and source exclusions remain in the
external-module assembly.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors
variable {H U : Type*} [Group H] [AddCommGroup U]
  [Module (ZMod 2) U]

/-- Both specified paired restrictions have dimension at least twelve. -/
theorem paired_dimension_lower
    (σ : Representation (ZMod 2) H U) (K X : Subgroup H)
    (eK : K ≃* BinaryLinearThree.Group) (h : PairedSetup σ K X eK) :
    12 ≤ Module.finrank (ZMod 2) U := by
  have hp := h.paired
  unfold PairedAlternatives at hp
  rcases hp with hs | hn
  · obtain ⟨e⟩ := hs
    have hd := e.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod, BinaryLinearThree.finrank_steinberg] at hd
    omega
  · obtain ⟨e⟩ := hn
    have hd := e.toLinearEquiv.finrank_eq
    have hv : Module.finrank (ZMod 2) BinaryLinearThree.Vector = 3 := by
      simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]
    simp only [Module.finrank_prod, Subspace.dual_finrank_eq, hv] at hd
    omega

variable [FiniteDimensional (ZMod 2) U]

/-- Conditional assembly of the three independent local calculations. The
normal-three and centralizing-actor premises must be proved before this yields
the full paired outer-actor theorem. -/
theorem paired_outer_bound_of_local_calculations
    (σ : Representation (ZMod 2) H U) (K X : Subgroup H)
    (eK : K ≃* BinaryLinearThree.Group) (h : PairedSetup σ K X eK)
    (hthree : ∀ A, IsElementaryTwo A → IsQuadratic σ A →
      ¬ A ≤ Subgroup.centralizer (X : Set H) →
      rank A = 1 ∧ 2 * fixedCodim σ A = Module.finrank (ZMod 2) U)
    (hrank : ∀ A, IsElementaryTwo A → A ≤ Subgroup.centralizer (X : Set H) → rank A ≤ 2)
    (houter : ∀ a : H, a ^ 2 = 1 → a ∉ K →
      a ∈ Subgroup.centralizer (X : Set H) → 6 ≤ fixedCodim σ (Subgroup.zpowers a))
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic σ A) (hout : ¬ A ≤ K) :
    2 * rank A < fixedCodim σ A := by
  have hdim := paired_dimension_lower σ K X eK h
  by_cases hc : A ≤ Subgroup.centralizer (X : Set H)
  · have hr := hrank A hA hc
    have ha : ∃ a ∈ A, a ∉ K := by
      by_contra! hh
      exact hout hh
    obtain ⟨a, ha, haK⟩ := ha
    let : IsElementaryAbelian 2 A := hA.2
    have hl := houter a (elemPow_eq_one_of_isElementaryAbelian a ha) haK (hc ha)
    have hz : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
    have hfix : fixedSpace σ A ≤ fixedSpace σ (Subgroup.zpowers a) := by
      intro v hv b
      exact hv ⟨b.val, hz b.property⟩
    have hfd := Submodule.finrank_mono hfix
    have hdA := fixedCodim_add_finrank σ A
    have hda := fixedCodim_add_finrank σ (Subgroup.zpowers a)
    omega
  · obtain ⟨hr, hd⟩ := hthree A hA hq hc
    omega

/-- Every nontrivial elementary quadratic actor outside the component has
fixed codimension strictly greater than twice its rank. All three local
calculations are discharged from the actual structural and module setup. -/
theorem paired_outer_bound [Finite H]
    (σ : Representation (ZMod 2) H U) (K X : Subgroup H)
    (eK : K ≃* BinaryLinearThree.Group) (h : PairedSetup σ K X eK)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic σ A) (hout : ¬ A ≤ K) :
    2 * rank A < fixedCodim σ A := by
  apply paired_outer_bound_of_local_calculations σ K X eK h
    (paired_normalThree_quadratic_rank_fixedCodim σ K X eK h)
    (centralizing_rank_le_two h) ?_ A hA hq hout
  intro a ha2 haK haX
  exact outer_involution_fixedCodim_ge_six σ K X eK h a ha2 haX
    (outerOnComponent_of_centralizing_involution h a ha2 haK haX)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors
