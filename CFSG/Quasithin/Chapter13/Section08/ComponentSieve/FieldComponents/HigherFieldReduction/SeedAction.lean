module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryOffender.Defs

/-!
# From Borel fixed vectors to the source seed contradiction

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955
(combined manuscript, 1 March 2004), the natural L₂ and odd-degree L₃ cases.

The module carrier is the additive form of the literal quotient U_H/V₁,
with U_H = ⟨V₃^H⟩. The action of H/O₂(H) must satisfy the exact conjugation
formula. Fixation of a quotient vector is equivalent to a commutator in V₁.
Thus a fixed-space calculation on the actual subgroup K* gives [V₃,K]≤V₁.
Relative normalization propagates this to U_H, and the earlier source
identity C_H(U_H/V₁)=O₂(H) contradicts the nontrivial image K*.

No abstract module of the same dimension replaces the source quotient.
The Borel-centralization and fixed-space premises remain explicit here;
NaturalLayers derives the latter from actual natural tensor section maps.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
variable {G : Type*} [Group G]

/-- A seed centralizer bound modulo V₁ propagates to its full H-conjugate span. -/
theorem UH_commutator_le_of_seed (H K V₃ V₁ : Subgroup G)
    (hVH : V₃ ≤ H) (hHK : H ≤ normalizer K) (hHV₁ : H ≤ normalizer V₁)
    (hseed : ⁅V₃, K⁆ ≤ V₁) : ⁅Source.UH H V₃, K⁆ ≤ V₁ := by
  let U := Source.UH H V₃
  have hHU : H ≤ normalizer U := le_normalizer_conjugateSpanBy V₃ H
  have hUV₁ : U ≤ normalizer V₁ := (conjugateSpanBy_le_self hVH).trans hHV₁
  have hs : V₃ ≤ commutatorPreimage U K V₁ :=
    le_commutatorPreimage (le_conjugateSpanBy V₃ H) hseed
  have hn : H ≤ normalizer (commutatorPreimage U K V₁) :=
    commutatorPreimage_normalized U K V₁ H hUV₁ hHU hHK hHV₁
  exact (commutator_mono (conjugateSpanBy_le hs hn) le_rfl).trans
    (commutator_commutatorPreimage_le U K V₁ hUV₁)

/-- With the actual kernel C_H(Ũ_H) = Q_H, the seed bound puts K in Q_H. -/
theorem component_le_QH_of_seed (H K V₃ V₁ : Subgroup G)
    (hKH : K ≤ H) (hVH : V₃ ≤ H) (hHK : H ≤ normalizer K)
    (hHV₁ : H ≤ normalizer V₁) (hseed : ⁅V₃, K⁆ ≤ V₁)
    (hkernel : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H) :
    K ≤ Source.QH H := by
  rw [← hkernel]
  apply le_commutatorPreimage hKH
  rw [commutator_comm]
  exact UH_commutator_le_of_seed H K V₃ V₁ hVH hHK hHV₁ hseed


/-- A nontrivial component image cannot centralize the seed modulo V₁.
The action kernel is the source equality Q_H = C_H(Ũ_H). -/
theorem seed_not_centralized_by_component (H K V₃ V₁ : Subgroup G)
    (hKH : K ≤ H) (hVH : V₃ ≤ H) (hHK : H ≤ normalizer K)
    (hHV₁ : H ≤ normalizer V₁)
    (hkernel : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
    (hne : Source.starImage H K ≠ ⊥) : ¬ ⁅V₃, K⁆ ≤ V₁ := by
  intro hseed
  have hK := component_le_QH_of_seed H K V₃ V₁ hKH hVH hHK hHV₁ hseed hkernel
  apply hne
  apply (map_eq_bot_iff (f := QuotientGroup.mk' (pCore 2 H)) _).mpr
  rw [QuotientGroup.ker_mk']
  intro k hk
  have hkQ := hK hk
  obtain ⟨q, hq, he⟩ := hkQ
  exact (Subtype.ext he : q = k) ▸ hq

namespace SeedAction
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The additive carrier of the literal source quotient U_H/V₁. -/
abbrev Space := Additive (Source.Utilde H V₃ V₁)

/-- The class of an element of U_H in the source binary module. -/
def vector (v : Source.UH H V₃) : Space H V₃ V₁ :=
  Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) v)

/-- Conjugation preserves the actual H-conjugate span defining U_H. -/
def conjugate (h : H) (u : Source.UH H V₃) : Source.UH H V₃ :=
  ⟨h.val * u.val * h.val⁻¹,
    le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H) h.val h.property
      u.val u.property⟩

/-- Compatibility with conjugation on the literal quotient; no module classification is assumed. -/
def IsConjugation (ρ : Representation (ZMod 2) (Source.Hstar H) (Space H V₃ V₁)) : Prop :=
  ∀ (h : H) (u : Source.UH H V₃),
    ρ (QuotientGroup.mk' (pCore 2 H) h) (vector H V₃ V₁ u) =
      vector H V₃ V₁ (conjugate H V₃ h u)

/-- A fixed source vector means exactly a commutator in V₁. -/
theorem fixes_vector_iff
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Space H V₃ V₁))
    (hρ : IsConjugation H V₃ V₁ ρ) (h : H) (u : Source.UH H V₃) :
    ρ (QuotientGroup.mk' (pCore 2 H) h) (vector H V₃ V₁ u) = vector H V₃ V₁ u ↔
      ⁅(h : G), (u : G)⁆ ∈ V₁ := by
  rw [hρ]
  change QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) (conjugate H V₃ h u) =
    QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u ↔ _
  simpa only [QuotientGroup.mk'_apply, mem_subgroupOf, coe_div, conjugate,
    div_eq_mul_inv, commutatorElement_def, coe_mul, coe_inv] using
    (QuotientGroup.eq_iff_div_mem
      (N := V₁.subgroupOf (Source.UH H V₃)) (x := conjugate H V₃ h u) (y := u))

/-- Fixed-space containment on K* turns the B-centralized seed into a K-centralized seed. -/
theorem seed_commutator_le_of_star_fixedSpace
    (K B : Subgroup G) (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Space H V₃ V₁))
    (hρ : IsConjugation H V₃ V₁ ρ) (hseed : ⁅V₃, B⁆ ≤ V₁)
    (hfixed : fixedSpace (ρ.comp (Source.starImage H K).subtype)
        ((Source.starImage H B).subgroupOf (Source.starImage H K)) ≤
      Representation.invariants (ρ.comp (Source.starImage H K).subtype)) :
    ⁅V₃, K⁆ ≤ V₁ := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro k hk v hv
  let u : Source.UH H V₃ := ⟨v, le_conjugateSpanBy V₃ H hv⟩
  have hvB : vector H V₃ V₁ u ∈
      fixedSpace (ρ.comp (Source.starImage H K).subtype)
        ((Source.starImage H B).subgroupOf (Source.starImage H K)) := by
    intro b
    obtain ⟨bH, hbH, he⟩ := b.property
    change QuotientGroup.mk' (pCore 2 H) bH = b.val.val at he
    change ρ b.val.val (vector H V₃ V₁ u) = vector H V₃ V₁ u
    rw [← he]
    apply (fixes_vector_iff H V₃ V₁ ρ hρ bH u).mpr
    have hc := commutator_le.mp hseed v hv bH.val hbH
    rw [← commutatorElement_inv]
    exact V₁.inv_mem hc
  let kstar : Source.starImage H K :=
    ⟨QuotientGroup.mk' (pCore 2 H) ⟨k, hKH hk⟩, ⟨⟨k, hKH hk⟩, hk, rfl⟩⟩
  exact (fixes_vector_iff H V₃ V₁ ρ hρ ⟨k, hKH hk⟩ u).mp (hfixed hvB kstar)

/-- The source kernel identity rules out a B-centralized seed when every B*-fixed vector is K*-fixed. -/
theorem contradiction_of_star_fixedSpace
    (K B : Subgroup G) (hKH : K ≤ H) (hVH : V₃ ≤ H)
    (hHK : H ≤ normalizer K) (hHV₁ : H ≤ normalizer V₁)
    (hkernel : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
    (hne : Source.starImage H K ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Space H V₃ V₁))
    (hρ : IsConjugation H V₃ V₁ ρ) (hseed : ⁅V₃, B⁆ ≤ V₁)
    (hfixed : fixedSpace (ρ.comp (Source.starImage H K).subtype)
        ((Source.starImage H B).subgroupOf (Source.starImage H K)) ≤
      Representation.invariants (ρ.comp (Source.starImage H K).subtype)) : False :=
  seed_not_centralized_by_component H K V₃ V₁ hKH hVH hHK hHV₁ hkernel hne
    (seed_commutator_le_of_star_fixedSpace H V₃ V₁ K B hKH ρ hρ hseed hfixed)
end SeedAction
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction

end
