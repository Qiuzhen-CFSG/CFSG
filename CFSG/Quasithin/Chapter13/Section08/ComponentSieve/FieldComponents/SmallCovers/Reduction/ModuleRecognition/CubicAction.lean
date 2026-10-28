module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.Residual
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.ScalarTransport
public import Theory.Representation.CubicComponentFaithfulness
public import Theory.Representation.BinaryOffender.IrreducibleExistence

/-!
# The cubic action on the actual source quotient

The genuine intrinsic cover identification and the seed commutator identity
construct a primitive cubic operator on the literal U_H/V₁. The component's
centralizer bound then proves faithfulness on every nonzero invariant submodule
and proper invariant quotient. A nonzero quotient also has an actual Irr⁺
submodule by perfect-actor existence. Its T-homogeneous refinement and
H-invariance are not asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.21(2),
printed p.956, and the section-faithfulness step of F.9.18(6), pp.325–326.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
variable {G : Type*} [Group G] [Finite G]
variable (H K V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The actual reduced cover supplies its primitive cubic polynomial before
any irreducible module is chosen. The seed equality is in the literal quotient. -/
theorem exists_residual_cubic_polynomial (act : QuotientAction H V₃ V₁)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (hseed : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H (coverResidualIn K)) = seedSpace H V₃ V₁) :
    ∃ z ∈ Source.starImage H K, orderOf z = 3 ∧
      zpowers z = Source.starImage H (coverResidualIn K) ∧
      CubicPolynomial act.representation z := by
  obtain ⟨z, hz, ho, hgen⟩ := ModuleRecognition.exists_residual_generator H K hKH hK e
  refine ⟨z, hz, ho, hgen, cubicPolynomial_of_moved act.representation z ?_ ?_⟩
  · rw [← ho]
    exact pow_orderOf_eq_one z
  · rw [hgen]
    exact residual_generates_quotient H V₃ V₁ act K hKH hseed

/-- The source quotient's nonzero submodules and proper quotients are faithful
under the explicit component-centralizer bound. This bound is a structural
input from the reduced configuration, not an FF or dimension conclusion. -/
theorem source_sections_faithful (act : QuotientAction H V₃ V₁)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (hcent : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤
      Source.starImage H K)
    (hseed : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H (coverResidualIn K)) = seedSpace H V₃ V₁) :
    (∀ W : Subrepresentation act.representation, W ≠ ⊥ →
      Function.Injective W.toRepresentation) ∧
    (∀ W : Subrepresentation act.representation, W ≠ ⊤ →
      Function.Injective W.quotientRepresentation) := by
  let L := Source.starImage H K
  let c : L ≃* HexEvenAutomorphisms :=
    (Components.componentStarEquiv H K hKH hK).symm.trans e
  let : Theory.GroupTheory.IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : Theory.GroupTheory.IsQuasisimple L :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv c.symm
  let : L.Normal := (inferInstance : (K.subgroupOf H).Normal).map
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  obtain ⟨z, hz, ho, hgen, hp⟩ :=
    exists_residual_cubic_polynomial H K V₃ V₁ act hKH hK e hseed
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  have hcz : centralizer (L : Set (Source.Hstar H)) ≤ zpowers z := by
    rw [hgen, ModuleRecognition.residual_star_eq_center H K hKH hK hc]
    intro x hx
    refine ⟨⟨x, hcent hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro l
    apply Subtype.ext
    exact mem_centralizer_iff.mp hx l l.property
  exact ⟨fun W hW => faithful_subrepresentation_of_cubicPolynomial
      act.representation L z hz ho hcz hp W hW,
    fun W hW => faithful_quotient_of_cubicPolynomial
      act.representation L z hz ho hcz hp W hW⟩

/-- Actual Irr⁺ existence, before the additional homogeneous choice and
invariance arguments. Nontriviality follows in the source from its rank-two seed. -/
theorem exists_source_irrPlus [Nontrivial (Additive (Source.Utilde H V₃ V₁))]
    (act : QuotientAction H V₃ V₁)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (hseed : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H (coverResidualIn K)) = seedSpace H V₃ V₁) :
    ∃ I, IsIrrPlus act.representation (Source.starImage H K) I := by
  let L := Source.starImage H K
  let c : L ≃* HexEvenAutomorphisms :=
    (Components.componentStarEquiv H K hKH hK).symm.trans e
  let : Theory.GroupTheory.IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : Theory.GroupTheory.IsQuasisimple L :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv c.symm
  obtain ⟨z, hz, _, _, hp⟩ :=
    exists_residual_cubic_polynomial H K V₃ V₁ act hKH hK e hseed
  apply exists_isIrrPlus_of_not_fixed act.representation L
  intro hfixed
  obtain ⟨v, hv⟩ := exists_ne (0 : Additive (Source.Utilde H V₃ V₁))
  exact hv (hp.fixed_eq_zero (hfixed Submodule.mem_top ⟨z, hz⟩))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
