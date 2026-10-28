module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.MainForward.SourceFamilies
public import CFSG.Quasithin.Chapter6.SourceDefs
public import CFSG.Quasithin.ClassificationModels.Families
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.Notation
public import Theory.Representation.BinaryPermutationAlternatingActions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Basic
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The standing source configuration for the conditional 13.8.5 assembly

The global record retains every clause of Hypothesis 13.3.1 and the
Sp₆(2), U₄(3) counterexample exclusions. The Lie and sporadic exclusions
use actual constructed carriers, and proper-K uses the full catalogue.
The local data retain the natural A₆ action of L/O₂,Z(L), the actual
R₂(LT) location and Sylow flag, and the abelian span of 13.8.2.

Faithfulness of the natural A₆ action identifies its kernel with C_L(V),
so the quotient in Hypothesis 13.7.1 is the same actual local quotient.
Exponent two propagates to the abelian conjugate span, proving that U_H
is elementary abelian. The order-two line lies in U_H by the flag.
These are hypothesis and applicability constructions, not a proof of
13.8.1 or of its earlier universal local theorems.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, p.877; Hypothesis 13.3.1 and Notation 13.3.3, pp.884–885;
Hypothesis 13.7.1, p.935; standing §13.8 configuration, pp.946–947.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u
/-- The actual Lie carriers over even fields larger than the prime field,
including all ranks and all twisted families in characteristic two. -/
def LargerEvenFieldModel (G : Type u) [Group G] : Prop :=
  ∃ f : ℕ, 1 < f ∧
    ((∃ n : ℕ, ClassicalGroup.IsPSL G n (2 ^ f) ∨
      ClassicalGroup.IsPSU G n (2 ^ f) ∨ ClassicalGroup.IsPSp G n (2 ^ f) ∨
      ClassicalGroup.IsPOmegaPlus G n (2 ^ f) ∨
      ClassicalGroup.IsPOmegaOdd G n (2 ^ f) ∨
      ClassicalGroup.IsPOmegaMinus G n (2 ^ f)) ∨
    ClassificationModels.IsG2At G (2 ^ f) ∨
    ExceptionalGroup.IsF4 G (2 ^ f) ∨ ExceptionalGroup.IsE6 G (2 ^ f) ∨
    ExceptionalGroup.IsE7 G (2 ^ f) ∨ ExceptionalGroup.IsE8 G (2 ^ f) ∨
    ExceptionalGroup.IsTwistedE6 G (2 ^ f) ∨
    Triality.Standard.IsTrialityGroupAt (2 ^ f) G ∨
    (∃ m : ℕ, f = 2 * m + 1 ∧
      (Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∨
       Nonempty (G ≃* ReeF4.Model m))))

variable {G : Type u} [Group G] [Finite G]
/-- Hypothesis 13.3.1 with the two additional exclusions of 13.7.1.
The local A₆ quotient is supplied by `LocalSetup` below. -/
structure Counterexample (T : Sylow 2 G) (L : Subgroup G) : Prop where
  qtke : IsSimpleQTKE KnownSimple.IsKnownSimple G
  local_component : L ∈ MainForward.faithfulLocalComponents T
  no_larger_field : ¬ LargerEvenFieldModel G
  no_linear : ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL G n 2
  no_alternating_nine : ¬ Nonempty (G ≃* alternatingGroup (Fin 9))
  no_sporadic : ∀ s : KnownSimple.SporadicName,
    s = .m22 ∨ s = .m23 ∨ s = .m24 ∨ s = .he ∨ s = .j4 →
      ¬ Nonempty (G ≃* s.Carrier)
  five_minimal : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ K ∈ MainForward.faithfulLocalComponents T,
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
  no_symplectic_six : ¬ ClassicalGroup.IsPSp G 3 2
  no_unitary_four : ¬ ClassicalGroup.IsPSU G 4 3

/-- The intrinsic O₂,Z(L), not its ambient image. -/
abbrev centralCore (L : Subgroup G) : Subgroup L :=
  (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L))

/-- The source L₁=O²(N_LT(V₁)); normalizer and two-residual conventions
are the ones in Notation 13.2.1. -/
abbrev sourceOne (L : Subgroup G) (T : Sylow 2 G) (V₁ : Subgroup G) : Subgroup G :=
  ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.one
    L (T : Subgroup G) V₁

/-- The actual local A₆ action and Sylow flag of the standing configuration.
The abelian conjugate span is precisely 13.8.2. No component recognition,
full H* model, or local quotient alternative of 13.8.5 is a field here. -/
structure LocalSetup (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G) where
  counterexample : Counterexample T L
  normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G)
  normalizes_V : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
  local_quotient : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6)
  module_in_reduced : V ≤ Chapter6.Source.reducedSubgroup (L ⊔ (T : Subgroup G))
  coordinate : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6))
  conjugation : ∀ (l : L) (v : V),
    (coordinate (V.normalizerMonoidHom
      ⟨l.val, normalizes_V (show l.val ∈ L ⊔ (T : Subgroup G) from mem_sup_left l.property)⟩ v)).toAdd =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (local_quotient (QuotientGroup.mk' (centralCore L) l)) (coordinate v).toAdd
  line_le_plane : V₁ ≤ V₂
  plane_le_seed : V₂ ≤ V₃
  seed_le : V₃ ≤ V
  line_card : Nat.card V₁ = 2
  plane_card : Nat.card V₂ = 4
  seed_card : Nat.card V₃ = 8
  line_stable : (T : Subgroup G) ≤ normalizer (V₁ : Set G)
  plane_stable : (T : Subgroup G) ≤ normalizer (V₂ : Set G)
  seed_stable : (T : Subgroup G) ≤ normalizer (V₃ : Set G)
  first_normalizer : G₁ = normalizer (V₁ : Set G)
  local_normalizer : M = normalizer (L : Set G)
  abelian_span : IsMulCommutative (conjugateSpanBy V G₁)

namespace LocalSetup
variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Faithfulness of the natural A₆ module identifies the intrinsic kernel
with C_L(V), proving the quotient convention required by 13.7.1. -/
theorem centralCore_eq_centralizer :
    centralCore L = (centralizer (V : Set G)).subgroupOf L := by
  ext l
  change l ∈ centralCore L ↔ l.val ∈ centralizer (V : Set G)
  constructor
  · intro hl
    have hq : QuotientGroup.mk' (centralCore L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    apply mem_centralizer_iff.mpr
    intro v hv
    have he := d.conjugation l ⟨v, hv⟩
    rw [hq, map_one, map_one, Module.End.one_apply] at he
    have he' := congrArg Subtype.val (d.coordinate.injective he)
    change l.val * v * l.val⁻¹ = v at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  · intro hl
    apply (QuotientGroup.eq_one_iff l).mp
    apply d.local_quotient.injective
    rw [map_one]
    apply ComponentSieve.SixAndG2.NaturalSix.alternatingAction_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v, hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    have hv' : (d.coordinate v).toAdd = w := hv
    have hc : V.normalizerMonoidHom
        ⟨l.val, d.normalizes_V (mem_sup_left l.property)⟩ v = v := by
      apply Subtype.ext
      change l.val * v.val * l.val⁻¹ = v.val
      rw [← mem_centralizer_iff.mp hl v.val v.property, mul_inv_cancel_right]
    have he := d.conjugation l v
    rw [hc, hv'] at he
    simpa only [ComponentSieve.SixAndG2.NaturalSix.alternatingAction,
      QuotientGroup.mk'_apply, map_one, Module.End.one_apply] using he.symm

/-- The abelian span of the actual natural module has exponent two. -/
theorem span_elementary : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := by
  let : IsMulCommutative (closure {x : G | ∃ g ∈ G₁, ∃ v ∈ V, g * v * g⁻¹ = x}) :=
    d.abelian_span
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨g, hg, v, hv, rfl⟩
  have hv2 : v ^ 2 = 1 := by
    have he : (⟨v, hv⟩ : V) ^ 2 = 1 := by
      apply d.coordinate.injective
      rw [map_pow, map_one, pow_two]
      change (d.coordinate ⟨v, hv⟩).toAdd + (d.coordinate ⟨v, hv⟩).toAdd = 0
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact congrArg Subtype.val he
  rw [conj_pow, hv2, mul_one, mul_inv_cancel]

/-- The literal U_H is elementary abelian, derived from 13.8.2 and the flag. -/
theorem uh_elementary {H : Subgroup G}
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M) :
    IsElementaryAbelian 2 (Source.UH H V₃) := by
  let := d.span_elementary
  exact IsElementaryAbelian.of_le (conjugateSpanBy_mono d.seed_le hH.2.1)

/-- The order-two line really lies in the quotient numerator. -/
theorem line_le_uh (H : Subgroup G) : V₁ ≤ Source.UH H V₃ :=
  (d.line_le_plane.trans d.plane_le_seed).trans (le_conjugateSpanBy V₃ H)
end LocalSetup

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

end
