module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.LocalFusion.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.LocalFusion.Reductions

/-!
# The local-fusion assembly for Aschbacher's Lemma 3.4

This module records the exact interface between the local transporter argument
on pp.94--96 of Aschbacher's paper and the final product-fusion paragraph.
The factor part is proved from the source hypotheses and global strong closure:
Sylow conjugacy inside the intersection-generated subgroup gives unique
conjugate membership for every nonidentity element of either factor.  The
product paragraph is kept as an explicit local input, since it is the step
which uses the involution centralizer alternatives (d)--(g) and the
dihedral/semidihedral recognition results.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4, pp.94--96, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The product-fusion paragraph of Lemma 3.4, isolated with the exact
conclusion consumed by `FusionConclusion.product_unique`.  Its hypotheses are
deliberately elementwise: the local proof may discharge them using the
centralizer calculation (g), quotient induction, and the two-group models
without exposing those implementation details in the public conclusion. -/
def ProductFusionInput (A₁ A₂ : Subgroup G) : Prop :=
  ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂,
    orderOf a₁ = 2 → orderOf a₂ = 2 → a₁ * a₂ ≠ 1 →
      UniqueConjugateMembership (intersectionGenerated A₁ A₂) (a₁ * a₂)

/-- Assemble the exact `FusionConclusion` once the global strong-closure step
and the product-fusion paragraph have been proved. -/
theorem fusionConclusion_of_productFusion
    {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (h : Hypotheses S A₁ A₂)
    (hclosed : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    (hproduct : ProductFusionInput A₁ A₂) :
    FusionConclusion S A₁ A₂ := by
  refine ⟨hclosed, ?_, ?_⟩
  · intro a ha hne
    exact h.unique_of_closed hclosed ha hne
  · exact hproduct

/-- A convenient wrapper for a local-fusion proof that supplies the factor
and product clauses separately.  This is the stable owner-facing boundary
used by the induction assembly; it does not assume Lemma 3.4 or Theorem 3.3.
-/
theorem fusionConclusion_of_local_fusion
    {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (h : Hypotheses S A₁ A₂)
    (hclosed : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    (hproduct : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂,
      orderOf a₁ = 2 → orderOf a₂ = 2 → a₁ * a₂ ≠ 1 →
        UniqueConjugateMembership (intersectionGenerated A₁ A₂) (a₁ * a₂)) :
    FusionConclusion S A₁ A₂ := by
  exact fusionConclusion_of_productFusion h hclosed hproduct

/-- An alternative assembly boundary matching the two contrary-fusion
arguments in the source. Only involutions from the factors and their nonidentity
mixed products need transporter control into S; the conclusion covers every
nonidentity factor element and all conjugates landing in H. Both transporter
premises remain proof obligations of the minimal-counterexample argument. -/
theorem fusionConclusion_of_sylow_transporters
    {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (h : Hypotheses S A₁ A₂)
    (hf : ∀ a ∈ (A₁ : Set G) ∪ A₂, orderOf a = 2 →
      ∀ g : G, g⁻¹ * a * g ∈ S → g ∈ intersectionGenerated A₁ A₂)
    (hp : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂,
      orderOf a₁ = 2 → orderOf a₂ = 2 → a₁ * a₂ ≠ 1 →
      ∀ g : G, g⁻¹ * (a₁ * a₂) * g ∈ S → g ∈ intersectionGenerated A₁ A₂) :
    FusionConclusion S A₁ A₂ := by
  have hc := h.closed_of_involution_transporters hf
  apply fusionConclusion_of_local_fusion h hc
  intro a₁ ha₁ a₂ ha₂ h₁ h₂ hne
  exact (uniqueConjugateMembership_iff_sylow_transporters
    (h.sylow_le_generated_of_closed hc)
    ((S : Subgroup G).mul_mem (h.left_le ha₁) (h.right_le ha₂))).mpr
      (hp a₁ ha₁ a₂ ha₂ h₁ h₂ hne)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
