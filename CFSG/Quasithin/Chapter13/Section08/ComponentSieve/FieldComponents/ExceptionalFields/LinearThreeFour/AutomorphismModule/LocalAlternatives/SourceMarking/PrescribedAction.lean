module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking.FactorTransport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.QuotientMarks

/-!
# The prescribed fixing and inverting action

Membership of t in L already makes it centralize L₀/O₂(L₀), by the
central-preimage definition. Inversion of X/O₂(X) by t also implies
inversion by t⁻¹. Both congruences therefore transport to the convention
used by sourceConjugation, without replacing t or assuming t² = 1.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004; Notation 13.2.1, p.877.
-/

@[expose] public section
noncomputable section
open Subgroup Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

theorem model_fix_zero (H K L : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hZH : zero L ≤ H) (hZK : zero L ≤ K)
    (t : H) (htL : t.val ∈ L) :
    ∀ x ∈ modelImage H K (zero L) eK,
      sourceConjugation H K eK (QuotientGroup.mk' (pCore 2 H) t) x * x⁻¹ ∈
        (modelImage H K (zero L) eK).pCoreIn 2 := by
  apply model_fix H K (zero L) eK hZH hZK t
  intro x hx
  have h := (coreAction_eq_one_iff _ _).mp
    (L_centralizes_zero_quotient L ⟨t.val⁻¹, L.inv_mem htL⟩) ⟨x, hx⟩
  refine ⟨_, h, ?_⟩
  change t.val⁻¹ * x * (t.val⁻¹)⁻¹ * x⁻¹ = _
  rw [inv_inv]

theorem model_invert_of_coreAction (H K D : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hDH : D ≤ H) (hDK : D ≤ K)
    (t : H) (htD : t.val ∈ normalizer (D : Set G))
    (ht : ∀ q : D ⧸ pCore 2 D, coreAction D ⟨t.val, htD⟩ q = q⁻¹) :
    ∀ x ∈ modelImage H K D eK,
      sourceConjugation H K eK (QuotientGroup.mk' (pCore 2 H) t) x * x ∈
        (modelImage H K D eK).pCoreIn 2 := by
  have hti : ∀ q : D ⧸ pCore 2 D, coreAction D (⟨t.val, htD⟩⁻¹) q = q⁻¹ := by
    intro q
    rw [map_inv]
    apply (coreAction D ⟨t.val, htD⟩).injective
    rw [MulAut.apply_inv_self, map_inv, ht, inv_inv]
  apply model_invert H K D eK hDH hDK t
  intro x hx
  let xn : D := ⟨x, hx⟩
  let tn : normalizer (D : Set G) := ⟨t.val, htD⟩
  have he := hti (QuotientGroup.mk' (pCore 2 D) xn)
  rw [coreAction_mk] at he
  have hm : D.normalizerMonoidHom tn⁻¹ xn * xn ∈ pCore 2 D := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 D) (_ * _) = 1
    rw [map_mul, he, inv_mul_cancel]
  refine ⟨_, hm, ?_⟩
  change t.val⁻¹ * x * (t.val⁻¹)⁻¹ * x = _
  rw [inv_inv]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
