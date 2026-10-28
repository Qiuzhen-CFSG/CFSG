module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase.Marks
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase.ModelCore
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!+# The inner prescribed actor gives the external-X alternative

This is the conditional inner branch in Aschbacher–Smith 13.8.20,
printed p.954/PDF p.971. X is L₁ in the ordinary A₆ case and the literal
commutator residual L₁,+ in the covered case. The hypotheses retain the
actual definitions from Notation 13.2.1, the earlier cubic quotient orders,
relative normality of K from 13.8.16, H=KL₁T and the actual higher-field model.
The preceding local Borel argument supplies normalization of the constructed
B and inversion by the prescribed t in T∩L.

All seven models give O₂(B*)=T*∩K*. Therefore X* normalizes this Sylow.
An inner prescribed actor has the same action as an element s of that
Sylow, and s⁻¹t* lies in C_T*(K*). Mutual normalization makes s act trivially
modulo O₂(X); two-perfectness then forces X* into C_H*(K*). Generation and
the normalizing two-group kernel lift normality to X itself. The actual
core quotient identifies X* as cubic, and s⁻¹t* inverts all of X*.

This route uses fewer local Borel identities than the printed torus route:
the B_C and index-three calculations are not needed for the inner branch.
It also does not need to select a case of the literal 13.8.14 Fitting
alternative; the quotient comparison used below is its independent,
proved subnormal-core interface. No Fitting conclusion is smuggled in as
standing data.

The kernel C_T*(K*) is retained. The literal source fixer equality still
requires the additional kernel containment identified by
TorusModels.Assembly.Model.conjugation_fixers_eq_sylow_iff. That equality
is neither assumed nor claimed here. The source owner must discharge the
preceding local inputs and combine this branch with the outer-actor result.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase
open Components.Fitting TorusModels.Assembly
universe u v
variable {G : Type u} [Group G]

/-- The displacement hypothesis below is exactly inversion on the intrinsic
two-core quotient through the actual conjugation action. -/
theorem inversion_mod_core_iff (X : Subgroup G) (t : normalizer (X : Set G)) :
    (∀ q : X ⧸ pCore 2 X,
      quotientAut (pCore 2 X) (X.normalizerMonoidHom t) q = q⁻¹) ↔
      ∀ x ∈ X, t.val * x * t.val⁻¹ * x ∈ X.pCoreIn 2 := by
  constructor
  · intro h x hx
    let y : X := ⟨x, hx⟩
    have he : X.normalizerMonoidHom t y * y ∈ pCore 2 X := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom t y * y) = 1
      rw [map_mul, ← quotientAut_apply_mk, h, inv_mul_cancel]
    exact ⟨X.normalizerMonoidHom t y * y, he, rfl⟩
  · intro h q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
    rw [quotientAut_apply_mk]
    apply mul_eq_one_iff_eq_inv.mp
    rw [← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (mem_map_iff_mem X.subtype_injective).mp (h x.val x.property)

variable [Finite G]

/-- The conditional inner-actor branch, with the Borel core calculation
discharged for every actual higher-field model. No externality, centralization,
normality of X, or centralizing inverter is an input. -/
theorem external_of_inner_markedActor {n : ℕ} {unitary four : Bool}
    (H K L L₁ T V₁ X : Subgroup G)
    (hKH : K ≤ H) (hLH : L₁ ≤ H) (hgen : H = K ⊔ (L₁ ⊔ T))
    (hT : Chapter1.IsSylowIn 2 T H) [(K.subgroupOf H).Normal]
    [(Source.starImage H K).Normal]
    (hdef : L₁ = (pResidual 2 (markedParabolic L T V₁)).map
      (markedParabolic L T V₁).subtype)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hmark : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = L₁) ∨
      (IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = markedPlus L L₁ T))
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hcover : IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nat.card (markedPlus L L₁ T ⧸ pCore 2 (markedPlus L L₁ T)) = 3)
    (model : Model.{u,v} (Source.starImage H K) n unitary four) (hn : 1 < n)
    (hB : L₁ ⊔ T ≤ normalizer (borel H K T hKH hT : Set G))
    (t : H) (ht : t.val ∈ T ⊓ L)
    (hinv : ∀ x ∈ X, t.val * x * t.val⁻¹ * x ∈ X.pCoreIn 2)
    (hi : markedActor H K T t ht.1 ∈ MulAut.innerSubgroup (Source.starImage H K)) :
    ExternalXAlternative H K X := by
  have hcard : Nat.card (X ⧸ pCore 2 X) = 3 := by
    rcases hmark with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact ha6 h
    · exact hcover h
  exact external_of_marked_borel_core H K L L₁ T V₁ X hKH hLH hgen hT hdef hTL hTV
    hmark hcard hB (model_residual_twoCore model hn (sourceSylow H K T hT)) t ht hinv hi

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase
