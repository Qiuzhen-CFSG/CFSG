module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.OrbitModels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags.Geometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags.AugmentationExtension
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.SectionStructure.SourceAction

/-!
# Assembly of the compatible source flags

For the actual H*=H/O₂(H) acting on U_H/V₁, extend the marked alternating
component action in the natural and augmentation cases. The literal product
H=KT and relative C-component membership give normality in H. The source
centralizer bound gives faithfulness; in the cover case its natural quotient
is also proved faithful by the intrinsic augmentation extension.

The actual ambient Sylow subgroup supplies a single coordinate permutation.
Conjugating the component marking and the full action by that permutation
identifies both actual section images with the canonical point and plane.
The cover argument uses exactly Ṽ₃=⟨Ṽ₂^J⟩ (with J=L₁ in the source), not a
stronger equality of the preimage groups. Every nonzero cover-plane vector
retains weight four. The same coordinates give all three hypotheses consumed
by `Marking.residual_and_quotient_of_marked_preimage`; no image of K₂ or its
quotient is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the first
proof paragraph of 13.8.6, printed p.948; 13.7.6(3) and its proof, pp.938–939;
and §B.3, pp.83–85. The earlier point witness, section dimensions, generation,
normalizers, order of V₁ and centralizer bound remain explicit source inputs.
Their applicability and the other clauses of 13.8.6 belong to the parent
parabolic-marking assembly.
-/

public section

open Subgroup Module BinaryPermutation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags
open TransvectionRecognition
open Theory.SpecificGroups.SymmetricSix

/-- The actual product H=KT makes the relative C-component normal in H,
and hence its actual image normal in H*. No ambient normality is imposed. -/
theorem source_component_normal {G : Type*} [Group G] [Finite G] (H K : Subgroup G) (T : Sylow 2 G)
    (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G)) :
    (Source.starImage H K).Normal := by
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
  let _ := TransvectionQuotients.FourLocalFactors.SectionStructure.component_normal_of_product
    H K T hKH hTH hK T.isPGroup' (fun h => by
      have hh : (h : G) ∈ (H : Set G) := h.property
      rw [hprod] at hh
      exact hh)
  exact Subgroup.Normal.map inferInstance (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _)

private theorem conjugate_compatible {A U W : Type*} [Group A]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A U)
    (r : Representation (ZMod 2) (Equiv.Perm (Fin 6)) W)
    (φ : A →* Equiv.Perm (Fin 6)) (E : U ≃ₗ[ZMod 2] W)
    (he : ∀ a u, E (ρ a u) = r (φ a) (E u)) (g : Equiv.Perm (Fin 6)) :
    ∀ a u, r g⁻¹ (E (ρ a u)) =
      r (((MulAut.conj g⁻¹).toMonoidHom.comp φ) a) (r g⁻¹ (E u)) := by
  intro a u
  change r g⁻¹ (E (ρ a u)) = r (g⁻¹ * φ a * (g⁻¹)⁻¹) (r g⁻¹ (E u))
  rw [he]
  change (r g⁻¹ * r (φ a)) (E u) =
    (r (g⁻¹ * φ a * (g⁻¹)⁻¹) * r g⁻¹) (E u)
  rw [← map_mul, ← map_mul]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

private theorem alternating_le_conjugate_range {A : Type*} [Group A]
    (φ : A →* Equiv.Perm (Fin 6))
    (ha : alternatingGroup (Fin 6) ≤ φ.range) (g : Equiv.Perm (Fin 6)) :
    alternatingGroup (Fin 6) ≤ ((MulAut.conj g⁻¹).toMonoidHom.comp φ).range := by
  intro a ha'
  obtain ⟨b, hb⟩ := ha ((inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem a ha' g)
  refine ⟨b, ?_⟩
  change g⁻¹ * φ b * (g⁻¹)⁻¹ = a
  rw [hb]
  simp [mul_assoc]
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags
open TransvectionRecognition
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] {H V₃ V₂ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The actual source centralizer bound makes the augmentation action faithful;
the intrinsic extension also proves faithfulness of its actual natural quotient. -/
theorem augmentation_extension (K : Subgroup G) [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (heK : ∀ k : Source.starImage H K, ∀ u,
      E (ρ k u) = alternatingCoreRepresentation (Fin 6) (eK k) (E u)) :
    ∃ φ : Source.Hstar H →* Equiv.Perm (Fin 6), Function.Injective φ ∧
      (∀ k : Source.starImage H K, φ k = (eK k).val) ∧
      (∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u)) ∧
      alternatingGroup (Fin 6) ≤ φ.range ∧
      (∀ a u, coreToNatural (Fin 6) (E (ρ a u)) =
        naturalRepresentation (Fin 6) (φ a) (coreToNatural (Fin 6) (E u))) ∧
      Function.Injective ((naturalRepresentation (Fin 6)).comp φ) :=
  AugmentationExtension.faithful_extension (Source.starImage H K) ρ
    (faithful_of_centralizer_le_core ρ hρ hcentralizer) eK E heK

/-- Natural source flags and the literal quotient-centralizer image in one
compatible coordinate system. Only the point witness is supplied by 13.7.6(3);
the two-dimensional plane is derived from Sylow invariance and dimension. -/
theorem natural_compatible_marking [Finite G] (T : Sylow 2 G) (K : Subgroup G)
    (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (heK : ∀ k : Source.starImage H K, ∀ u,
      E (ρ k u) = alternatingNaturalRepresentation (Fin 6) (eK k) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.naturalPointSpace)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hTV₃ : (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (hdim₃ : finrank (ZMod 2) (sectionImage H V₃ V₁ V₃) = 2)
    (hV₂ : V₂ ≤ Source.UH H V₃) (hHZ : H ≤ normalizer (V₁ : Set G))
    (hV₁ : Nat.card V₁ = 2) :
    ∃ (g : Equiv.Perm (Fin 6)) (φ : Source.Hstar H →* Equiv.Perm (Fin 6)),
      Function.Injective φ ∧
      (∀ k : Source.starImage H K, φ k = g⁻¹ * (eK k).val * g) ∧
      (∀ a u, naturalRepresentation (Fin 6) g⁻¹ (E (ρ a u)) =
        naturalRepresentation (Fin 6) (φ a) (naturalRepresentation (Fin 6) g⁻¹ (E u))) ∧
      ((sectionImage H V₃ V₁ V₂).map E.toLinearMap).map
        (naturalRepresentation (Fin 6) g⁻¹) = OrbitModels.naturalPointSpace ∧
      ((sectionImage H V₃ V₁ V₃).map E.toLinearMap).map
        (naturalRepresentation (Fin 6) g⁻¹) = OrbitModels.plane.map (coreToNatural (Fin 6)) ∧
      (T : Subgroup G) ≤ commutatorPreimage H V₂ V₁ ∧
      H ≤ centralizer (V₁ : Set G) ∧
      (((commutatorPreimage H V₂ V₁).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.H1 ∨
        ((commutatorPreimage H V₂ V₁).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.L1) := by
  let _ := source_component_normal H K T hK hprod
  have hTH : (T : Subgroup G) ≤ H := by
    intro t ht
    change t ∈ (H : Set G)
    rw [hprod]
    exact ⟨1, K.one_mem, t, ht, one_mul t⟩
  obtain ⟨φ, hφ, hφK, hφE, hT, hH, _⟩ :=
    natural_source_outputs T K ρ hρ hcentralizer eK E heK hpoint hTH hTV₂ hV₂ hHZ hV₁
  have ha : alternatingGroup (Fin 6) ≤ φ.range := by
    intro a ha
    obtain ⟨k, hk⟩ := eK.surjective ⟨a, ha⟩
    exact ⟨k.val, by rw [hφK, hk]⟩
  have hd : finrank (ZMod 2) (sectionImage H V₃ V₁ V₂) = 1 := by
    rw [← E.finrank_map_eq, hpoint]
    exact finrank_span_singleton OrbitModels.naturalPoint_ne_zero
  obtain ⟨g, _, hp, hplane⟩ :=
    natural_source_flags T hTH ρ hρ φ ha E hφE hTV₂ hTV₃ hd hdim₃
  let r := naturalRepresentation (Fin 6)
  let ψ := (MulAut.conj g⁻¹).toMonoidHom.comp φ
  let E' := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (r.asGroupHom g⁻¹))
  have he' : ∀ a u, E' (ρ a u) = r (ψ a) (E' u) :=
    conjugate_compatible ρ r φ E hφE g
  have hp' : (sectionImage H V₃ V₁ V₂).map E'.toLinearMap = OrbitModels.naturalPointSpace := by
    rw [← hp, ← Submodule.map_comp]
    rfl
  refine ⟨g, ψ, (MulAut.conj g⁻¹).injective.comp hφ, ?_, he', hp, hplane, hT, hH, ?_⟩
  · intro k
    change g⁻¹ * φ k * (g⁻¹)⁻¹ = _
    rw [hφK, inv_inv]
  · exact natural_preimage_image ρ hρ ψ (alternating_le_conjugate_range φ ha g)
      E' he' hp' hV₂ hHZ

/-- Cover source flags and the literal quotient-centralizer image, without a
full extension premise. The natural quotient remains faithful, and every
nonzero vector of the actual cover plane has weight four before quotienting. -/
theorem augmentation_compatible_marking [Finite G] (T : Sylow 2 G) (K : Subgroup G)
    (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (heK : ∀ k : Source.starImage H K, ∀ u,
      E (ρ k u) = alternatingCoreRepresentation (Fin 6) (eK k) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.pointSpace)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hTV₃ : (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (hdim₃ : finrank (ZMod 2) (sectionImage H V₃ V₁ V₃) = 2)
    (J : Subgroup G)
    (hgen : sectionImage H V₃ V₁ V₃ = Submodule.span (ZMod 2)
      {v | ∃ a ∈ Source.starImage H J, ∃ x ∈ sectionImage H V₃ V₁ V₂, ρ a x = v})
    (hV₂ : V₂ ≤ Source.UH H V₃) (hHZ : H ≤ normalizer (V₁ : Set G))
    (hV₁ : Nat.card V₁ = 2) :
    ∃ (g : Equiv.Perm (Fin 6)) (φ : Source.Hstar H →* Equiv.Perm (Fin 6)),
      Function.Injective φ ∧
      (∀ k : Source.starImage H K, φ k = g⁻¹ * (eK k).val * g) ∧
      (∀ a u, coreRepresentation (Fin 6) g⁻¹ (E (ρ a u)) =
        coreRepresentation (Fin 6) (φ a) (coreRepresentation (Fin 6) g⁻¹ (E u))) ∧
      ((sectionImage H V₃ V₁ V₂).map E.toLinearMap).map
        (coreRepresentation (Fin 6) g⁻¹) = OrbitModels.pointSpace ∧
      ((sectionImage H V₃ V₁ V₃).map E.toLinearMap).map
        (coreRepresentation (Fin 6) g⁻¹) = OrbitModels.plane ∧
      (∀ v ∈ (sectionImage H V₃ V₁ V₃).map E.toLinearMap,
        v ≠ 0 → OrbitModels.weight v = 4) ∧
      (∀ a u, coreToNatural (Fin 6) (coreRepresentation (Fin 6) g⁻¹ (E (ρ a u))) =
        naturalRepresentation (Fin 6) (φ a)
          (coreToNatural (Fin 6) (coreRepresentation (Fin 6) g⁻¹ (E u)))) ∧
      Function.Injective ((naturalRepresentation (Fin 6)).comp φ) ∧
      (T : Subgroup G) ≤ commutatorPreimage H V₂ V₁ ∧
      H ≤ centralizer (V₁ : Set G) ∧
      (((commutatorPreimage H V₂ V₁).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.H1 ∨
        ((commutatorPreimage H V₂ V₁).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.L1) := by
  let _ := source_component_normal H K T hK hprod
  have hTH : (T : Subgroup G) ≤ H := by
    intro t ht
    change t ∈ (H : Set G)
    rw [hprod]
    exact ⟨1, K.one_mem, t, ht, one_mul t⟩
  obtain ⟨φ, hφ, hφK, hφE, ha, _, _⟩ := augmentation_extension K ρ hρ hcentralizer eK E heK
  obtain ⟨g, _, hp, hplane, hw⟩ := augmentation_flags_of_section_span T hTH ρ hρ φ ha E hφE
    hpoint hTV₂ hTV₃ hdim₃ J hgen
  let r := coreRepresentation (Fin 6)
  let ψ := (MulAut.conj g⁻¹).toMonoidHom.comp φ
  let E' := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (r.asGroupHom g⁻¹))
  have he' : ∀ a u, E' (ρ a u) = r (ψ a) (E' u) :=
    conjugate_compatible ρ r φ E hφE g
  have hp' : (sectionImage H V₃ V₁ V₂).map E'.toLinearMap = OrbitModels.pointSpace := by
    rw [← hp, ← Submodule.map_comp]
    rfl
  have hψ : Function.Injective ψ := (MulAut.conj g⁻¹).injective.comp hφ
  refine ⟨g, ψ, hψ, ?_, he', hp, hplane, hw, ?_, ?_, ?_⟩
  · intro k
    change g⁻¹ * φ k * (g⁻¹)⁻¹ = _
    rw [hφK, inv_inv]
  · intro a u
    change coreToNatural (Fin 6) (E' (ρ a u)) = _
    rw [he']
    exact coreToNatural_equivariant _ _
  · exact ComponentSieve.SixAndG2.NaturalSix.symmetricAction_injective.comp hψ
  · exact augmentation_source_outputs T ρ hρ ψ (alternating_le_conjugate_range φ ha g)
      E' he' hp' hTH hTV₂ hV₂ hHZ hV₁
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags
