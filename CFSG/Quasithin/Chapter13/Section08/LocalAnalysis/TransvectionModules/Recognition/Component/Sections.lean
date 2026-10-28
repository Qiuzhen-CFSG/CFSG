module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic

/-!
# The actual component section in the recognition argument

The additive image of U_K=[U_H,K] in U_H/V₁ equals the linear displacement
span for K*. This follows by transporting commutator generators through
the compatible conjugation action in both directions. The image is
K-invariant, so its quotient by its K-fixed vectors is the precise section
used by 13.7.6. The model predicate requires an actual group equivalence
and an equivariant linear equivalence for this section.

The definitions are shared by the component-selection and module-extension
steps. They do not assert the G.6.4 or 13.7.6 recognition conclusions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.7.6,
printed pp.938–940, and the first paragraph of 13.8.5, printed p.947.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component

variable {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The additive image of the literal U_K=[U_H,K] in U_H/V₁. -/
def commutatorImage (K : Subgroup G) :
    Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) :=
  AddSubgroup.toZModSubmodule 2
    (((⁅Source.UH H V₃, K⁆).subgroupOf (Source.UH H V₃)).map
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))).toAddSubgroup

variable {H V₃ V₁}

/-- Conjugation identifies the group commutator image with the linear displacement span. -/
theorem commutatorImage_eq_subspaceCommutator (K : Subgroup G) (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) :
    commutatorImage H V₃ V₁ K = subspaceCommutator ρ ⊤ (Source.starImage H K) := by
  let U := Source.UH H V₃
  let q : U →* Source.Utilde H V₃ V₁ := QuotientGroup.mk' (V₁.subgroupOf U)
  let S := subspaceCommutator ρ ⊤ (Source.starImage H K)
  let C := (S.toAddSubgroup.toSubgroup'.comap q).map U.subtype
  have hcU : ⁅U, K⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp
    (hKH.trans (le_normalizer_conjugateSpanBy V₃ H))
  have hcomm : ⁅U, K⁆ ≤ C := by
    apply commutator_le.mpr
    intro u hu k hk
    have hc := hcU (commutator_mem_commutator hu hk)
    refine ⟨⟨⁅u, k⁆, hc⟩, ?_, rfl⟩
    change vector H V₃ V₁ _ ∈ S
    rw [vector_commutator ρ hρ ⟨u, hu⟩ ⟨k, hKH hk⟩]
    apply S.neg_mem_iff.mp
    rw [neg_sub]
    exact Submodule.subset_span ⟨_, ⟨⟨k, hKH hk⟩, hk, rfl⟩,
      vector H V₃ V₁ ⟨u, hu⟩, Submodule.mem_top, rfl⟩
  apply le_antisymm
  · intro v hv
    obtain ⟨u, hu, he⟩ := hv
    obtain ⟨u', hu', heu⟩ := hcomm hu
    have huu : u' = u := Subtype.ext heu
    subst u'
    change Additive.ofMul (q u) ∈ S at hu'
    change q u = v.toMul at he
    simpa only [he, ofMul_toMul] using hu'
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ⟨h, hh, rfl⟩, v, _, rfl⟩
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf U) v.toMul
    have hv : vector H V₃ V₁ u = v := congrArg Additive.ofMul hu
    rw [← hv]
    apply (commutatorImage H V₃ V₁ K).neg_mem_iff.mp
    rw [neg_sub, ← vector_commutator ρ hρ u h]
    exact ⟨_, commutator_mem_commutator u.property hh, rfl⟩

/-- The actual K-action preserves the literal commutator image. -/
theorem commutatorImage_invariant (K : Subgroup G) (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (k : K) (u : commutatorImage H V₃ V₁ K) :
    ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u ∈
      commutatorImage H V₃ V₁ K := by
  obtain ⟨x, hx, he⟩ := u.property
  have hv : vector H V₃ V₁ x = (u : Additive (Source.Utilde H V₃ V₁)) :=
    congrArg Additive.ofMul he
  rw [← hv, hρ]
  refine ⟨_, ?_, rfl⟩
  exact (mem_normalizer_iff.mp (normalizer_commutator_ge_right (Source.UH H V₃) K
    k.property) x).mp hx

variable (H V₃ V₁)

/-- The fixed vectors of K in the actual commutator image. -/
noncomputable def fixedInCommutator
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (K : Subgroup G) : Submodule (ZMod 2) (commutatorImage H V₃ V₁ K) :=
  (fixedSpace ρ (Source.starImage H K)).comap (commutatorImage H V₃ V₁ K).subtype

/-- The literal section Ũ_K/C_{Ũ_K}(K) required by 13.7.6. -/
abbrev ComponentSection
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (K : Subgroup G) :=
  commutatorImage H V₃ V₁ K ⧸ fixedInCommutator H V₃ V₁ ρ K

/-- A model for the actual component section, retaining the same intrinsic
quotient identification on every representative. This is a conclusion
predicate, not an assumed recognition theorem. -/
def HasSectionModel
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (K : Subgroup G) (hKH : K ≤ H)
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) A E) (eK : (K ⧸ pCore 2 K) ≃* A) : Prop :=
  ∃ (hs : ∀ (k : K) (u : commutatorImage H V₃ V₁ K),
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u ∈ commutatorImage H V₃ V₁ K)
    (e : ComponentSection H V₃ V₁ ρ K ≃ₗ[ZMod 2] E),
    ∀ (k : K) (u : commutatorImage H V₃ V₁ K),
      e (Submodule.Quotient.mk ⟨ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u,
        hs k u⟩) = σ (eK (QuotientGroup.mk' (pCore 2 K) k)) (e (Submodule.Quotient.mk u))

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component

end
