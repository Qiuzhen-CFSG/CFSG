module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Faithfulness from the source component and Sylow product

A representation faithful on a normal subgroup with two-group quotient
has two-group kernel. In H/O₂(H) that normal kernel is trivial. Applying
this to the actual marked component and H=KT proves faithfulness in both
module cases, with no separate source-centralizer premise. Conjugation
compatibility then identifies the quotient centralizer inside O₂(H).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the setup
preceding 13.7.2 on p.935 and the hypotheses of 13.8.6 on p.948.
Only relative component normality is used; H=KT establishes it.
-/

public section
open Subgroup Module BinaryPermutation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
open TransvectionRecognition
variable {G : Type*} [Group G]

private theorem faithful_of_normal_two_quotient {A B : Type*} [Group A] [Monoid B]
    (f : A →* B) (K : Subgroup A) [K.Normal]
    (hK : Function.Injective (f.comp K.subtype))
    (hquot : IsPGroup 2 (A ⧸ K)) (hcore : pCore 2 A = ⊥) : Function.Injective f := by
  let q : f.ker →* A ⧸ K := (QuotientGroup.mk' K).comp f.ker.subtype
  have hq : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    have hxK : x.val ∈ K := (QuotientGroup.eq_one_iff x.val).mp hx
    have he : (⟨x.val, hxK⟩ : K) = 1 := hK (by
      change f x.val = f 1
      rw [map_one]
      exact x.property)
    change x = 1
    apply Subtype.ext
    exact congrArg (fun k : K => k.val) he
  have hp : IsPGroup 2 f.ker := hquot.of_injective q hq
  have hle : f.ker ≤ pCore 2 A := le_sSup ⟨inferInstance, hp⟩
  exact f.ker_eq_bot_iff.mp (le_bot_iff.mp (hle.trans hcore.le))

/-- The faithful component action extends faithfully to the actual H*. -/
theorem source_action_faithful [Finite G] (H K : Subgroup G) (T : Sylow 2 G)
    (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    {U W A : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (Source.Hstar H) U)
    (σ : Representation (ZMod 2) A W) (hσ : Function.Injective σ)
    (eK : Source.starImage H K ≃* A) (E : U ≃ₗ[ZMod 2] W)
    (he : ∀ (k : Source.starImage H K) u, E (ρ k u) = σ (eK k) (E u)) :
    Function.Injective ρ := by
  let _ := CompatibleFlags.source_component_normal H K T hK hprod
  have hKH : K ≤ H := by
    intro k hk
    change k ∈ (H : Set G)
    rw [hprod]
    exact ⟨k, hk, 1, (T : Subgroup G).one_mem, mul_one k⟩
  have hTH : (T : Subgroup G) ≤ H := by
    intro t ht
    change t ∈ (H : Set G)
    rw [hprod]
    exact ⟨1, K.one_mem, t, ht, one_mul t⟩
  have hKT : K ⊔ (T : Subgroup G) = H := by
    apply le_antisymm (sup_le hKH hTH)
    intro x hx
    have hx' : x ∈ (K : Set G) * (T : Set G) := hprod ▸ hx
    obtain ⟨k, hk, t, ht, rfl⟩ := hx'
    exact (K ⊔ (T : Subgroup G)).mul_mem ((show K ≤ K ⊔ (T : Subgroup G) from le_sup_left) hk)
      ((show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right) ht)
  have hs : Source.starImage H K ⊔ Source.starImage H T = ⊤ := by
    rw [Source.starImage, Source.starImage, ← Subgroup.map_sup, ← subgroupOf_sup hKH hTH,
      hKT, subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have ht : IsPGroup 2 (Source.starImage H T) := T.isPGroup'.comap_subtype.map _
  apply faithful_of_normal_two_quotient ρ (Source.starImage H K) ?_
    (isPGroup_quotient_of_sup_eq_top _ _ ht hs) (pCore_quotient_pCore_eq_bot 2)
  intro a b hab
  apply eK.injective
  apply hσ
  ext w
  obtain ⟨v, rfl⟩ := E.surjective w
  rw [← he, ← he]
  exact congrArg (fun f => E (f v)) hab

variable {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Recover the source quotient-centralizer bound from the constructed
faithful action, using its agreement with actual conjugation. -/
theorem source_centralizer_bound
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (hf : Function.Injective ρ)
    (hHZ : H ≤ normalizer (V₁ : Set G)) :
    commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H := by
  intro h hh
  let hH : H := ⟨h, commutatorPreimage_le H _ _ hh⟩
  have hfix : hH ∈ Representation.BinaryOffender.subspaceKernel
      (ρ.comp (QuotientGroup.mk' (pCore 2 H)))
      (sectionImage H V₃ V₁ (Source.UH H V₃)) ⊤ := by
    rw [← quotient_centralizer_preimage ρ hρ _ le_rfl hHZ]
    exact hh
  have he : ρ (QuotientGroup.mk' (pCore 2 H) hH) = ρ 1 := by
    rw [map_one]
    ext x
    apply hfix.2 x
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) x.toMul
    exact ⟨u, u.property, congrArg Additive.ofMul hu⟩
  exact ⟨hH, (QuotientGroup.eq_one_iff hH).mp (hf he), rfl⟩
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
