module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.SourceGeneration
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Source transport for the covered-A₆ product branch

Centralization by K* and normalization by the remaining generators imply
normality of X* in H*. The seed identity modulo V₁ gives its linear
commutator identity under the literal conjugation action, and normal seed
generation then gives [Ũ_H,X*] = Ũ_H. Centralization modulo V₁ similarly
retains the actual fixed seed. Intrinsic two-cores and the critical-pair
containment pass through the same product equivalence.

These are conditional assembly lemmas for Aschbacher–Smith 13.8.21(1),
printed p.957 (combined manuscript, 1 March 2004). The covered residual
placement, its seed action, and the marked product equivalence remain to
be constructed from the standing setup. No numbered source result is asserted.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
variable {G : Type*} [Group G]

private theorem starImage_normalizes (H A B : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H B : Set (Source.Hstar H)) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  refine ⟨a * b * a⁻¹, le_normalizer_iff.mp hAB a.val ha b.val hb, ?_⟩
  simp only [map_mul, map_inv]

/-- The centralizing star factor is normal once its other source generators
normalize it. No ambient normality of X is assumed. -/
theorem star_normal_of_source_generators (H K L₁ T X : Subgroup G)
    (hgen : H = K ⊔ (L₁ ⊔ T)) (hKH : K ≤ H) (hLH : L₁ ≤ H) (hTH : T ≤ H)
    (hcentral : Source.starImage H K ≤
      centralizer (Source.starImage H X : Set (Source.Hstar H)))
    (hLX : L₁ ≤ normalizer (X : Set G)) (hTX : T ≤ normalizer (X : Set G)) :
    (Source.starImage H X).Normal := by
  have he : Source.starImage H K ⊔ (Source.starImage H L₁ ⊔ Source.starImage H T) = ⊤ := by
    unfold Source.starImage
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← subgroupOf_sup hLH hTH,
      ← subgroupOf_sup hKH (sup_le hLH hTH), ← hgen]
    simp [subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  constructor
  intro x hx g
  have hn : (⊤ : Subgroup (Source.Hstar H)) ≤
      normalizer (Source.starImage H X : Set (Source.Hstar H)) := by
    rw [← he]
    exact sup_le (hcentral.trans (centralizer_le_normalizer _))
      (sup_le (starImage_normalizes H L₁ X hLX) (starImage_normalizes H T X hTX))
  exact le_normalizer_iff.mp hn g (mem_top g) x hx

variable [Finite G]

/-- Intrinsic two-cores pass through the literal star map. -/
theorem starImage_twoCore (H B : Subgroup G) (hBH : B ≤ H) :
    Source.starImage H (B.pCoreIn 2) = (Source.starImage H B).pCoreIn 2 := by
  have he : (B.pCoreIn 2).subgroupOf H = (B.subgroupOf H).pCoreIn 2 := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBH),
      map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hBH]
  change ((B.pCoreIn 2).subgroupOf H).map _ = _
  rw [he]
  exact map_pCoreIn_of_ker_isPGroup (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) (B.subgroupOf H)

/-- The chosen product map transports the two-core of every marked subgroup. -/
theorem marked_twoCore_image (H B : Subgroup G) (hBH : B ≤ H)
    (e : Source.Hstar H ≃* BinaryLinearThree.Group × Equiv.Perm (Fin 3)) :
    (Source.starImage H (B.pCoreIn 2)).map e.toMonoidHom =
      ((Source.starImage H B).map e.toMonoidHom).pCoreIn 2 := by
  rw [starImage_twoCore H B hBH]
  exact map_pCoreIn_of_injective 2 _ _ e.injective

/-- The source critical-pair containment is transported using that very same map. -/
theorem critical_le_marked_twoCore (H B A : Subgroup G) (hBH : B ≤ H)
    (hA : A ≤ B.pCoreIn 2)
    (e : Source.Hstar H ≃* BinaryLinearThree.Group × Equiv.Perm (Fin 3)) :
    (Source.starImage H A).map e.toMonoidHom ≤
      ((Source.starImage H B).map e.toMonoidHom).pCoreIn 2 := by
  rw [← marked_twoCore_image H B hBH e]
  exact map_mono (map_mono (comap_mono hA))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
open Representation.BinaryOffender
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The earlier seed identity modulo V₁ becomes the literal representation
commutator identity. It is not strengthened to an equality before quotienting. -/
theorem seed_commutator_of_group_generation (act : SourceAction H V₃ V₁)
    (X : Subgroup G) (hXH : X ≤ H) (hn : X ≤ normalizer (V₃ : Set G))
    (hgen : V₃ ≤ ⁅X,V₃⁆ ⊔ V₁) :
    subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H X) = seedSpace H V₃ V₁ := by
  let D := subspaceCommutator act.representation (seedSpace H V₃ V₁) (Source.starImage H X)
  let q := QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
  let N : Subgroup (Source.UH H V₃) := {
    carrier := {u | Additive.ofMul (q u) ∈ D}
    one_mem' := by
      change Additive.ofMul (q 1) ∈ D
      rw [map_one, ofMul_one]
      exact D.zero_mem
    mul_mem' := by
      intro a b ha hb
      change Additive.ofMul (q (a * b)) ∈ D
      rw [map_mul, ofMul_mul]
      exact D.add_mem ha hb
    inv_mem' := by
      intro a ha
      change Additive.ofMul (q a⁻¹) ∈ D
      rw [map_inv, ofMul_inv]
      exact D.neg_mem ha }
  have hline : V₁ ≤ N.map (Source.UH H V₃).subtype := by
    intro v hv
    refine ⟨⟨v,act.line_le hv⟩, ?_, rfl⟩
    change Additive.ofMul (q ⟨v,act.line_le hv⟩) ∈ D
    have hq : q ⟨v,act.line_le hv⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hv
    rw [hq]
    exact D.zero_mem
  have hcomm : ⁅X,V₃⁆ ≤ N.map (Source.UH H V₃).subtype := by
    apply commutator_le.mpr
    intro x hx v hv
    have hcv : ⁅x,v⁆ ∈ V₃ := by
      exact V₃.mul_mem (le_normalizer_iff.mp hn x hx v hv) (V₃.inv_mem hv)
    refine ⟨⟨⁅x,v⁆, le_conjugateSpanBy V₃ H hcv⟩, ?_, rfl⟩
    have hd : act.representation (QuotientGroup.mk' (pCore 2 H) ⟨x,hXH hx⟩)
        (seedVector H V₃ V₁ ⟨v,hv⟩) - seedVector H V₃ V₁ ⟨v,hv⟩ ∈ D :=
      Submodule.subset_span ⟨_, ⟨⟨x,hXH hx⟩, hx, rfl⟩, _,
        Submodule.subset_span ⟨⟨v,hv⟩,rfl⟩, rfl⟩
    rw [seedVector, act.conjugation] at hd
    change Additive.ofMul (q
      (conjugateUH H V₃ ⟨x,hXH hx⟩ ⟨v,le_conjugateSpanBy V₃ H hv⟩ *
        (⟨v,le_conjugateSpanBy V₃ H hv⟩ : Source.UH H V₃)⁻¹)) ∈ D
    simpa only [q, map_mul, map_inv, ofMul_mul, ofMul_inv,
      sub_eq_add_neg] using hd
  apply le_antisymm
  · apply subspaceCommutator_le_of_invariant
    apply le_subspaceStabilizer
    exact seedSpace_invariant H V₃ V₁ act X hn
  · apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl⟩
    obtain ⟨u, hu, he⟩ := (sup_le hcomm hline) (hgen v.property)
    have he' : u = (⟨v.val,le_conjugateSpanBy V₃ H v.property⟩ : Source.UH H V₃) :=
      Subtype.ext he
    change Additive.ofMul (q u) ∈ D at hu
    change Additive.ofMul (q ⟨v.val,le_conjugateSpanBy V₃ H v.property⟩) ∈ D
    simpa only [he'] using hu

/-- Normal source seed generation, with its module premise derived from the
earlier group commutator identity modulo V₁. -/
theorem full_commutator_of_group_generation (act : SourceAction H V₃ V₁)
    (X : Subgroup G) (hXH : X ≤ H) (hn : X ≤ normalizer (V₃ : Set G))
    (hgen : V₃ ≤ ⁅X,V₃⁆ ⊔ V₁) (hX : (Source.starImage H X).Normal) :
    subspaceCommutator act.representation ⊤ (Source.starImage H X) = ⊤ :=
  normal_seed_generation H V₃ V₁ act X hX
    (seed_commutator_of_group_generation H V₃ V₁ act X hXH hn hgen)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
open Representation.BinaryOffender
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Centralization of V₃/V₁ by the actual L₀ gives its fixed seed in Ũ_H.
This keeps the point-stabilizer relation attached to the source action. -/
theorem seed_fixed_of_group_commutator (act : SourceAction H V₃ V₁)
    (L₀ : Subgroup G) (hcomm : ⁅L₀,V₃⁆ ≤ V₁) :
    seedSpace H V₃ V₁ ≤ fixedSpace act.representation (Source.starImage H L₀) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v,rfl⟩ ⟨_,x,hx,rfl⟩
  change act.representation (QuotientGroup.mk' (pCore 2 H) x)
    (seedVector H V₃ V₁ v) = seedVector H V₃ V₁ v
  rw [seedVector, act.conjugation]
  let q := QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
  let u : Source.UH H V₃ := ⟨v.val,le_conjugateSpanBy V₃ H v.property⟩
  have hc : q (conjugateUH H V₃ x u * u⁻¹) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hcomm (commutator_mem_commutator hx v.property)
  rw [map_mul, map_inv, mul_inv_eq_one] at hc
  exact congrArg Additive.ofMul hc
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
