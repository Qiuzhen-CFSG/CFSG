module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.FixedSpace
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import Theory.Representation.G2Natural
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual block quotient models for the binary rank-two branches

A C.1 block model gives a conjugation model on the embedded U=[O₂(K),K].
The actor map is the specified isomorphism after K→K/O₂(K), and the module
map is the specified isomorphism after U→U/C_U(K). Its kernel and literal
conjugation law are proved, with no fixed-space conclusion assumed.

For the G₂ source predicate, its specified octonion projection induces an
actual linear equivalence from the canonical trace-zero scalar quotient.
Transport along this equivalence constructs the standard natural action,
retaining the original core quotient isomorphism and projection equivariance.
Source: Aschbacher–Smith, C.1.32 and Lemma 13.6.22, printed p.932.
-/

@[expose] public section

open Subgroup Representation CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.Models
variable {G A W : Type*} [Group G] [Group A] [AddCommGroup W] [Module (ZMod 2) W]
variable (K : Subgroup G) (ρ : Representation (ZMod 2) A W)

noncomputable def ambientU : Subgroup G := (blockU K).map K.subtype

noncomputable def ambientUEquiv : blockU K ≃* ambientU K :=
  (blockU K).equivMapOfInjective K.subtype K.subtype_injective

theorem ambientU_normalizes : K ≤ normalizer (ambientU K : Set G) := by
  intro k hk
  apply mem_normalizer_iff.mpr
  intro u
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(⟨k,hk⟩ : K) * x * (⟨k,hk⟩ : K)⁻¹,
      (blockU_normal K).conj_mem x hx ⟨k,hk⟩, rfl⟩
  · intro hu
    obtain ⟨x,hx,he⟩ := hu
    refine ⟨(⟨k,hk⟩ : K)⁻¹ * x * ⟨k,hk⟩,
      (by simpa using (blockU_normal K).conj_mem x hx (⟨k,hk⟩ : K)⁻¹), ?_⟩
    change k⁻¹ * (x : G) * k = u
    change (x : G) = k * u * k⁻¹ at he
    rw [he]
    group

noncomputable def blockQuotientModel
    (σ : A →* MulAut (Multiplicative W)) (b : BlockModuleModel K σ)
    (hσ : ∀ a w, Multiplicative.toAdd (σ a w) = ρ a (Multiplicative.toAdd w)) :
    ConjugationQuotientModel K (ambientU K) ρ where
  normalizes := ambientU_normalizes K
  actor := b.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  quotient := b.moduleIso.toMonoidHom.comp
    ((QuotientGroup.mk' (blockFixed K)).comp (ambientUEquiv K).symm.toMonoidHom)
  surjective := b.moduleIso.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (ambientUEquiv K).symm.surjective)
  kernel := by
    ext u
    obtain ⟨x,rfl⟩ := (ambientUEquiv K).surjective u
    change b.moduleIso (QuotientGroup.mk' (blockFixed K)
      ((ambientUEquiv K).symm ((ambientUEquiv K) x))) = 1 ↔ _
    rw [MulEquiv.symm_apply_apply, map_eq_one_iff b.moduleIso b.moduleIso.injective]
    change (QuotientGroup.mk x : BlockModule K) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    change (x : K) ∈ center K ↔ (x.val : G) ∈ centralizer (K : Set G)
    constructor
    · intro hx k hk
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨k,hk⟩)
    · intro hx
      exact mem_center_iff.mpr (fun k => Subtype.ext (hx k k.property))
  equivariant := by
    intro k u
    obtain ⟨x,rfl⟩ := (ambientUEquiv K).surjective u
    have he : (ambientU K).normalizerMonoidHom
        ⟨(k : G), ambientU_normalizes K k.property⟩ ((ambientUEquiv K) x) =
        (ambientUEquiv K) (blockConjugate K k x) := by
      apply Subtype.ext
      rfl
    change b.moduleIso (QuotientGroup.mk' (blockFixed K)
      ((ambientUEquiv K).symm _)) = _
    rw [he, MulEquiv.symm_apply_apply, b.intertwining]
    change σ (b.quotientIso (QuotientGroup.mk' (pCore 2 K) k))
      (b.moduleIso (QuotientGroup.mk' (blockFixed K) x)) =
      Multiplicative.ofAdd (ρ (b.quotientIso (QuotientGroup.mk' (pCore 2 K) k))
        (Multiplicative.toAdd (b.moduleIso (QuotientGroup.mk' (blockFixed K)
          ((ambientUEquiv K).symm ((ambientUEquiv K) x))))))
    rw [MulEquiv.symm_apply_apply]
    exact congrArg Multiplicative.ofAdd (hσ _ _)
theorem blockQuotientModel_actor_surjective
    (σ : A →* MulAut (Multiplicative W)) (b : BlockModuleModel K σ)
    (hσ : ∀ a w, Multiplicative.toAdd (σ a w) = ρ a (Multiplicative.toAdd w)) :
    Function.Surjective (blockQuotientModel K ρ σ b hσ).actor :=
  b.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

theorem blockQuotientModel_actor_kernel
    (σ : A →* MulAut (Multiplicative W)) (b : BlockModuleModel K σ)
    (hσ : ∀ a w, Multiplicative.toAdd (σ a w) = ρ a (Multiplicative.toAdd w)) :
    (blockQuotientModel K ρ σ b hσ).actor.ker = pCore 2 K := by
  change (b.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ b.quotientIso.injective, QuotientGroup.ker_mk']
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.Models

open Subgroup CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Atlas.G2.Natural
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.G2Models


noncomputable def sourceNaturalEquiv
    (π : octonionTraceZero →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hπ : Function.Surjective π) (hker : π.ker = octonionScalarLine) :
    Space (ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (π.quotKerEquivOfSurjective hπ)

theorem sourceNaturalEquiv_mk
    (π : octonionTraceZero →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hπ : Function.Surjective π) (hker : π.ker = octonionScalarLine)
    (x : TraceZero (ZMod 2)) :
    sourceNaturalEquiv π hπ hker (mk (ZMod 2) x) = π x := rfl

theorem sourceNaturalEquiv_action
    (σ : commutator (Atlas.G2.Model (ZMod 2)) →*
      MulAut (Multiplicative (Fin 6 → ZMod 2)))
    (π : octonionTraceZero →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hπ : Function.Surjective π) (hker : π.ker = octonionScalarLine)
    (he : ∀ (g : commutator (Atlas.G2.Model (ZMod 2))) (x y : octonionTraceZero),
      y.val = g.val.val x.val →
      π y = Multiplicative.toAdd (σ g (Multiplicative.ofAdd (π x))))
    (g : commutator (Atlas.G2.Model (ZMod 2))) (w : Space (ZMod 2)) :
    sourceNaturalEquiv π hπ hker (derivedAction (ZMod 2) g w) =
      Multiplicative.toAdd (σ g (Multiplicative.ofAdd (sourceNaturalEquiv π hπ hker w))) := by
  obtain ⟨x,rfl⟩ := mk_surjective (ZMod 2) w
  rw [derivedAction_mk, sourceNaturalEquiv_mk, sourceNaturalEquiv_mk]
  exact he g x (traceZeroAction (ZMod 2) g.val x) rfl

theorem g2_linearBlock {K : Type*} [Group K] (h : IsG2TwoBlock K) :
    IsLinearBlockModel K (derivedAction (ZMod 2)) := by
  obtain ⟨_, σ, ⟨b⟩, π, hπ, hker, he⟩ := h
  let e := sourceNaturalEquiv π hπ hker
  let eM := e.toAddEquiv.toMultiplicative
  let σ' : commutator (Atlas.G2.Model (ZMod 2)) →*
      MulAut (Multiplicative (Space (ZMod 2))) :=
    (MulAut.congr eM.symm).toMonoidHom.comp σ
  let b' : BlockModuleModel K σ' := {
    quotientIso := b.quotientIso
    moduleIso := b.moduleIso.trans eM.symm
    intertwining := by
      intro k u
      change eM.symm (b.moduleIso _) = eM.symm (σ _ (eM (eM.symm (b.moduleIso _))))
      rw [MulEquiv.apply_symm_apply, b.intertwining] }
  refine ⟨σ', ⟨b'⟩, ?_⟩
  intro g w
  apply e.injective
  change e (e.symm (Multiplicative.toAdd (σ g (eM w)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (sourceNaturalEquiv_action σ π hπ hker he g (Multiplicative.toAdd w)).symm
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.G2Models
