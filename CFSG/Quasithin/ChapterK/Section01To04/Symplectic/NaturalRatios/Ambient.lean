module
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.NaturalSource
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.NaturalOuter
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# The ambient natural symplectic action in Chapter K

Conjugating by a natural identification maps the original acting group into
the literal binary normalizer of the natural symplectic image. This map
intertwines the original representation and identifies the original component
with the actual matrix image. Transported normalizer conjugation is exactly
the conjugation action on that component, so it preserves the two parabolic
classes and is a product of an inner and a field automorphism.

The outer-offender calculation now places every ambient offender in the
original component. Centerlessness, simplicity and the trivial ambient
centralizer follow from the genuine generalized-Fitting and quasisimplicity
hypotheses, without additional covering or automorphism assumptions.

Source: Aschbacher–Smith, K.3.4.1, printed p.456 (PDF p.467).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch.Symplectic
namespace CFSG.Quasithin.ChapterK.Symplectic
set_option linter.unusedSectionVars false
variable {F G V : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

namespace NaturalIdentification
variable (h : NaturalIdentification (F := F) (ρ.comp L.subtype))

/-- The original action in the coordinates of the natural identification. -/
@[expose] noncomputable def ambientAction : G →* (Vector F ≃ₗ[ZMod 2] Vector F) :=
  linearAction (h.linearEquiv.conjRingEquiv.toMonoidHom.comp ρ)

/-- Evaluation of the transported action uses the specified linear equivalence. -/
lemma ambientAction_apply (g : G) (v : Vector F) :
    h.ambientAction g v = h.linearEquiv (ρ g (h.linearEquiv.symm v)) := rfl

/-- Faithfulness survives the change of module coordinates. -/
lemma ambientAction_injective (hf : Function.Injective ρ) :
    Function.Injective h.ambientAction :=
  linearAction_injective _ (fun _ _ he => hf (h.linearEquiv.conjRingEquiv.injective he))

/-- The component acts through the specified symplectic group isomorphism. -/
lemma ambientAction_component (g : L) :
    h.ambientAction g = SymplecticNaturalNormalizer.naturalHom (h.groupEquiv g) := by
  apply LinearEquiv.ext
  intro v
  rw [ambientAction_apply]
  change h.linearEquiv ((ρ.comp L.subtype) g (h.linearEquiv.symm v)) = _
  rw [h.intertwines, h.linearEquiv.apply_symm_apply]
  rfl

/-- The component image is the literal derived natural image. -/
lemma ambientAction_image (hcard : 2 < Nat.card F) :
    L.map h.ambientAction = naturalDerivedImage := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    rw [show h.ambientAction g = _ from h.ambientAction_component ⟨g,hg⟩]
    exact SymplecticNaturalNormalizer.naturalHom_mem hcard _
  · rintro _ ⟨g,rfl⟩
    let x := h.groupEquiv.symm g.val
    refine ⟨x,x.property,?_⟩
    have hx := h.ambientAction_component x
    rw [h.groupEquiv.apply_symm_apply] at hx
    exact hx

variable [L.Normal]

/-- Ambient normality gives membership in the actual binary normalizer. -/
lemma ambientAction_mem_normalizer (hcard : 2 < Nat.card F) (g : G) :
    h.ambientAction g ∈ naturalNormalizer := by
  change h.ambientAction g ∈ normalizer (naturalDerivedImage (F := F))
  rw [← h.ambientAction_image hcard]
  apply Subgroup.le_normalizer_map
  exact mem_map_of_mem h.ambientAction (by rw [L.normalizer_eq_top]; trivial)

/-- The ambient group mapped into the literal natural normalizer. -/
@[expose] noncomputable def normalizerHom (hcard : 2 < Nat.card F) :
    G →* naturalNormalizer (F := F) :=
  h.ambientAction.codRestrict _ (h.ambientAction_mem_normalizer hcard)

/-- The normalizer map is an embedding for a faithful original action. -/
lemma normalizerHom_injective (hcard : 2 < Nat.card F) (hf : Function.Injective ρ) :
    Function.Injective (h.normalizerHom hcard) :=
  fun _ _ he => h.ambientAction_injective hf (congrArg Subtype.val he)

/-- The normalizer map retains the original representation. -/
lemma normalizerHom_intertwines (hcard : 2 < Nat.card F) (g : G) (v : V) :
    h.linearEquiv (ρ g v) =
      naturalNormalizerAction (h.normalizerHom hcard g) (h.linearEquiv v) := by
  change _ = h.ambientAction g (h.linearEquiv v)
  rw [ambientAction_apply, h.linearEquiv.symm_apply_apply]

/-- Normalizer conjugation is the actual ambient conjugation on the component. -/
lemma normalizerHom_conjugation (hcard : 2 < Nat.card F) (g : G) :
    SymplecticNaturalNormalizer.conjugation hcard (h.normalizerHom hcard g) =
      extensionAction L h.groupEquiv.symm g := by
  apply MulEquiv.ext
  intro x
  apply SymplecticNaturalNormalizer.naturalHom_injective
  rw [SymplecticNaturalNormalizer.conjugation_apply]
  have hc (y : Sp F) :
      h.ambientAction (h.groupEquiv.symm y).val = SymplecticNaturalNormalizer.naturalHom y := by
    simpa only [MulEquiv.apply_symm_apply] using h.ambientAction_component (h.groupEquiv.symm y)
  rw [← hc, ← hc]
  change h.ambientAction g * h.ambientAction _ * (h.ambientAction g)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, extensionAction_apply]

/-- Every induced automorphism preserves both actual parabolic conjugacy classes. -/
lemma preservesDiagram (hcard : 2 < Nat.card F) (g : G) :
    PreservesDiagram (extensionAction L h.groupEquiv.symm g) := by
  rw [← h.normalizerHom_conjugation hcard g]
  exact SymplecticNaturalNormalizer.conjugation_preservesDiagram hcard _

/-- Every induced automorphism is inner times a field automorphism. -/
lemma semilinear_conjugation (hcard : 2 < Nat.card F) (g : G) :
    ∃ (x : Sp F) (σ : F ≃+* F),
      extensionAction L h.groupEquiv.symm g = MulAut.conj x * fieldAutomorphism σ := by
  rw [← h.normalizerHom_conjugation hcard g]
  exact SymplecticNaturalNormalizer.conjugation_semilinear hcard _

include h in
/-- The proved outer exclusion places every original offender inside L. -/
lemma offender_le {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 1 < r)
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : IsOffender ρ A) : A ≤ L := by
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hr
  have ho := hA.map_equivariant ρ naturalNormalizerAction (h.normalizerHom hcard)
    (h.normalizerHom_injective hcard hf) h.linearEquiv (h.normalizerHom_intertwines hcard)
  have hc := Natural.offender_le_natural_image hF hr ho
  intro a ha
  have hm : h.ambientAction a ∈ naturalDerivedImage :=
    hc (mem_map_of_mem (h.normalizerHom hcard) ha)
  rw [← h.ambientAction_image hcard] at hm
  obtain ⟨b,hb,he⟩ := hm
  exact h.ambientAction_injective hf he ▸ hb

end NaturalIdentification

end CFSG.Quasithin.ChapterK.Symplectic

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.ChapterK.Symplectic
variable {F G V : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {K : GroupClass}

/-- The source component is normal because it is the generalized Fitting subgroup. -/
theorem SourceHypothesis.component_normal (hs : SourceHypothesis K ρ L) : L.Normal := by
  let := hs.finite_group
  rw [← hs.fitting]
  infer_instance

omit [Finite F] in
/-- The actual matrix identification makes the component centerless. -/
theorem NaturalIdentification.component_center_eq_bot
    (h : NaturalIdentification (F := F) (ρ.comp L.subtype)) : center L = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hm : h.groupEquiv x ∈ center (Sp F) := MulEquivClass.apply_mem_center h.groupEquiv hx
  rw [EvenProjective.center_eq_bot, mem_bot] at hm
  exact h.groupEquiv.injective (hm.trans h.groupEquiv.map_one.symm)

omit [Finite F] in
/-- Centerlessness reduces the source quasisimple component to a simple group. -/
theorem NaturalIdentification.component_simple (hs : SourceHypothesis K ρ L)
    (h : NaturalIdentification (F := F) (ρ.comp L.subtype)) : IsSimpleGroup L := by
  let : IsQuasisimple L := hs.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq h.component_center_eq_bot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

omit [Finite F] in
/-- Self-centralization of F*(G) makes the ambient component centralizer trivial. -/
theorem NaturalIdentification.component_centralizer (hs : SourceHypothesis K ρ L)
    (h : NaturalIdentification (F := F) (ρ.comp L.subtype)) : centralizer (L : Set G) = ⊥ := by
  let := hs.finite_group
  apply le_bot_iff.mp
  intro x hx
  have hle : centralizer (L : Set G) ≤ L := by
    rw [← hs.fitting]
    exact centralizer_generalizedFitting_le G
  have hz : (⟨x,hle hx⟩ : L) ∈ center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) y y.property)
  rw [h.component_center_eq_bot, mem_bot] at hz
  exact congrArg Subtype.val hz

end CFSG.Quasithin.ChapterK.Symplectic
