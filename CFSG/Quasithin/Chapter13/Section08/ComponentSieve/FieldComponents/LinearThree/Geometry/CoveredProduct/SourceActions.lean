module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ComponentAutomorphisms

/-!
# Covered source component geometry and its seed action

The earlier natural covered action, the literal Fitting alternative of
13.8.14, relative component normality and the source Sylow subgroup now
produce the residual placement, inner component action, and corrected
inverter together. The resulting witness retains every original quotient
and subgroup map. It is an output of `source_component_geometry`, not an
additional standing hypothesis.

The source seed commutators then give full normal-seed generation and the
fixed seed under L₀*. These are the group and action inputs to the marked
L₃(2) × S₃ product and its later tensor consumer; that product and the tensor
exclusion are not asserted by this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
covered paragraph of 13.8.21(1), printed p.957.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
open ResidualPlacement
variable {G : Type*} [Group G]

/-- Derived group geometry, with the actual source inverter and seed retained. -/
structure SourceComponentGeometry (H K L T V₁ V₃ : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group) where
  zero_le : zero L ≤ K
  component_not_normalizes : ¬ K ≤ normalizer (zero L : Set G)
  zero_not_centralizing : ¬ Source.starImage H K ≤
    centralizer (Source.starImage H (zero L) : Set (Source.Hstar H))
  plus_centralized : Source.starImage H K ≤
    centralizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H))
  plus_normal : (Source.starImage H (plus L T V₁)).Normal
  plus_card : Nat.card (Source.starImage H (plus L T V₁)) = 3
  one_factorization : (Source.starImage H (one L T V₁) : Set (Source.Hstar H)) =
    (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)) *
      (Source.starImage H (zero L) : Set (Source.Hstar H))
  placement : ParabolicPlacement H K L T eK
  inner_action : ∀ h : Source.Hstar H, ∃ k : Source.starImage H K,
    ∀ x : Source.starImage H K, h * x.val * h⁻¹ = k.val * x.val * k.val⁻¹
  inverter : (T ⊓ L : Subgroup G)
  inverter_mem : inverter.val ∈ H
  inverter_normalizes_plus : inverter.val ∈ normalizer (plus L T V₁ : Set G)
  inverter_quotient_action : ∀ x : plus L T V₁ ⧸ pCore 2 (plus L T V₁),
    coreAction (plus L T V₁) ⟨inverter.val,inverter_normalizes_plus⟩ x = x⁻¹
  inverter_zero_action : coreAction (zero L)
    ⟨inverter.val,L_normalizes_zero L inverter.property.2⟩ = 1
  inverter_component_action : ∀ x : Source.starImage H K,
    QuotientGroup.mk' (pCore 2 H) ⟨inverter.val,inverter_mem⟩ * x.val *
      (QuotientGroup.mk' (pCore 2 H) ⟨inverter.val,inverter_mem⟩)⁻¹ = x.val
  inverter_plus_action : ∀ x ∈ Source.starImage H (plus L T V₁),
    QuotientGroup.mk' (pCore 2 H) ⟨inverter.val,inverter_mem⟩ * x *
      (QuotientGroup.mk' (pCore 2 H) ⟨inverter.val,inverter_mem⟩)⁻¹ = x⁻¹
  plus_seed_normalizes : plus L T V₁ ≤ normalizer (V₃ : Set G)
  seed_moved : V₃ ≤ ⁅plus L T V₁,V₃⁆ ⊔ V₁
  seed_zero_fixed : ⁅zero L,V₃⁆ ≤ V₁

/-- Construct the component geometry from genuine earlier source inputs.
No residual placement, inner action, inverter or product is assumed. -/
theorem source_component_geometry [Finite G] (H K L T V V₁ V₃ M : Subgroup G)
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (one L T V₁ ⊔ T))
    (hnot : ¬ one L T V₁ ≤ K)
    (hKM : ¬ K ≤ M) (hNM : normalizer (zero L : Set G) ≤ M)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (hfit : fittingPreimageResidual H = ⊥ ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        fittingPreimageResidual H = one L T V₁) ∨
      fittingPreimageResidual H = plus L T V₁) :
    Nonempty (SourceComponentGeometry H K L T V₁ V₃ eK) := by
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hDH : one L T V₁ ≤ H := by rw [hgen]; exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  let : (Source.starImage H K).Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  obtain ⟨hz,hkn,hzc,hc,hn,hcard,hfac,⟨p⟩,⟨hXN,hseed,hzseed⟩,_⟩ :=
    source_placement H K L T V V₁ V₃ M d hfactor hgen hnot hKM hNM S hS eK hfit
  obtain ⟨t,htH,ht,ht₀,htK,htX⟩ := source_centralizing_inverter H K L T V V₁ V₃ d
    eK p hKH hDH hTH hfactor hz hn hc
  exact ⟨{
    zero_le := hz
    component_not_normalizes := hkn
    zero_not_centralizing := hzc
    plus_centralized := hc
    plus_normal := hn
    plus_card := hcard
    one_factorization := hfac
    placement := p
    inner_action := source_inner_action H K L T V₁ eK p d.normalizes_L hgen hfactor hz hc
    inverter := t
    inverter_mem := htH
    inverter_normalizes_plus := T_normalizes_plus L T V₁ d.normalizes_L d.line_stable t.property.1
    inverter_quotient_action := ht
    inverter_zero_action := ht₀
    inverter_component_action := htK
    inverter_plus_action := htX
    plus_seed_normalizes := hXN
    seed_moved := hseed
    seed_zero_fixed := hzseed }⟩

open Representation.BinaryOffender
open scoped IsMulCommutative
variable (H K L T V₁ V₃ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The derived group geometry supplies both the normal-seed commutator
identity and the fixed seed for the first-factor parabolic. -/
theorem source_seed_actions
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (geo : SourceComponentGeometry H K L T V₁ V₃ eK)
    (act : SourceAction H V₃ V₁) (hXH : plus L T V₁ ≤ H) :
    subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H (plus L T V₁)) = seedSpace H V₃ V₁ ∧
    subspaceCommutator act.representation ⊤ (Source.starImage H (plus L T V₁)) = ⊤ ∧
    seedSpace H V₃ V₁ ≤ fixedSpace act.representation (Source.starImage H (zero L)) := by
  exact ⟨seed_commutator_of_group_generation H V₃ V₁ act _ hXH
      geo.plus_seed_normalizes geo.seed_moved,
    full_commutator_of_group_generation H V₃ V₁ act _ hXH
      geo.plus_seed_normalizes geo.seed_moved geo.plus_normal,
    seed_fixed_of_group_commutator H V₃ V₁ act _ geo.seed_zero_fixed⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
