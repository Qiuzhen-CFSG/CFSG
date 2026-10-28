module
public import CFSG.Quasithin.Chapter5.Section03SymplecticSource.MarkedRecognition
public import Theory.SpecificGroups.SymplecticFour.SourceNormalizerExtension
public import Theory.GroupTheory.Amalgam.AutomorphismTransport

/-!
# Extending automorphisms of the native symplectic amalgam

Construct the pure inner extension of Sp₄(F) and transport the literal native
pair to it. A compatible pair automorphism twists the inclusion completion on
the same carrier, without changing its full overlap or order. Marked symplectic
recognition therefore gives an automorphism retaining both endpoint maps.
Transporting back yields surjectivity of native restriction. Its established
injectivity forces a unique homomorphic lift of every marked action.

The order bound here is reflexivity on the concrete extension carrier; no
source-group order or source-group recognition is used. The nonbinary case
includes q = 4 and retains both endpoint orientations.

Source: the compatible realization step of Aschbacher–Smith 5.3.2, p.659,
proved using the marked refinement of F.4.8–10,16–17 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter5.Section03SymplecticSource
open ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

/-- The actual inner automorphism subgroup, with its two native parabolics. -/
def pureInner : SourceExtension F where
  carrier := inner F
  left := pointParabolic.map MulAut.conj
  right := planeParabolic.map MulAut.conj
  left_le := Subgroup.map_le_range _ _
  right_le := Subgroup.map_le_range _ _
  contains_inner := le_rfl
  preserves_diagram := by
    rintro _ ⟨g,rfl⟩
    exact DiagramAutomorphisms.inner_preservesDiagram g
  left_inner := inf_eq_left.mpr (Subgroup.map_le_range _ _)
  right_inner := inf_eq_left.mpr (Subgroup.map_le_range _ _)
  factor := by
    rintro _ ⟨g,rfl⟩
    exact ⟨g,1,one_mem _,(mul_one _).symm⟩

/-- Conjugation transports all three groups of the native diagram together. -/
def pureComparison : RankTwoAmalgam.Iso (SourceNormalizerExtension.diagram F)
    (pureInner (F := F)).amalgam where
  left := pointParabolic.equivMapOfInjective MulAut.conj SourceExtension.inner_injective
  middle := (borel.equivMapOfInjective MulAut.conj SourceExtension.inner_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_inf _ _ _ SourceExtension.inner_injective))
  right := planeParabolic.equivMapOfInjective MulAut.conj SourceExtension.inner_injective
  left_commutes _ := by apply Subtype.ext; rfl
  right_commutes _ := by apply Subtype.ext; rfl

/-- Centerlessness identifies the native group with the pure inner carrier. -/
def pureCarrierEquiv : Sp F ≃* (pureInner (F := F)).carrier :=
  MonoidHom.ofInjective SourceExtension.inner_injective

variable [Finite F]

/-- Twisting the marking leaves the native order unchanged, so marked recognition
extends every compatible automorphism of an extension diagram. -/
theorem extension_amalgam_automorphism {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) (E : SourceExtension F)
    (a : RankTwoAmalgam.Iso E.amalgam E.amalgam) :
    ∃ f : MulAut E.carrier,
      (∀ x, f (E.modelCompletion.left x) = E.modelCompletion.left (a.left x)) ∧
      (∀ x, f (E.modelCompletion.right x) = E.modelCompletion.right (a.right x)) := by
  let d := E.modelCompletion.comapIso a
  have ho : d.left.range ⊓ d.right.range = d.middle.range := by
    simpa only [d, RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using E.model_overlap
  obtain ⟨f,hl,hr⟩ := Completion.exists_marked_mulEquiv_of_card_le d hF hn ho le_rfl
  refine ⟨f.symm, ?_, ?_⟩
  · intro x
    rw [←hl x, f.symm_apply_apply]
    rfl
  · intro x
    rw [←hr x, f.symm_apply_apply]
    rfl

/-- The native group automorphism retains both given endpoint automorphisms. -/
theorem native_amalgam_automorphism {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (a : RankTwoAmalgam.Iso (SourceNormalizerExtension.diagram F)
      (SourceNormalizerExtension.diagram F)) :
    ∃ f : MulAut (Sp F),
      (∀ x : pointParabolic (F := F), f x.val = (a.left x).val) ∧
      (∀ x : planeParabolic (F := F), f x.val = (a.right x).val) := by
  let e := pureComparison (F := F)
  let b := RankTwoAmalgam.automorphismConjEquiv e a
  obtain ⟨f,hl,hr⟩ := extension_amalgam_automorphism hF hn pureInner b
  let z := pureCarrierEquiv (F := F)
  refine ⟨z.trans (f.trans z.symm), ?_, ?_⟩
  · intro x
    apply z.injective
    change z (z.symm (f (z x.val))) = z (a.left x).val
    rw [z.apply_symm_apply]
    change f (pureInner.modelCompletion.left (e.left x)) =
      pureInner.modelCompletion.left (e.left (a.left x))
    rw [hl]
    congr 1
    change e.left (a.left (e.left.symm (e.left x))) = _
    rw [e.left.symm_apply_apply]
  · intro x
    apply z.injective
    change z (z.symm (f (z x.val))) = z (a.right x).val
    rw [z.apply_symm_apply]
    change f (pureInner.modelCompletion.right (e.right x)) =
      pureInner.modelCompletion.right (e.right (a.right x))
    rw [hr]
    congr 1
    change e.right (a.right (e.right.symm (e.right x))) = _
    rw [e.right.symm_apply_apply]

private theorem map_eq_of_marked {U : Type*} [Group U]
    (P : Subgroup U) (f : MulAut U) (a : MulAut P)
    (h : ∀ x : P, f x.val = (a x).val) : P.map f.toMonoidHom = P := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change f x ∈ P
    rw [h ⟨x,hx⟩]
    exact (a ⟨x,hx⟩).property
  · intro x hx
    refine ⟨(a.symm ⟨x,hx⟩).val, (a.symm ⟨x,hx⟩).property, ?_⟩
    exact (h _).trans (congrArg Subtype.val (a.apply_symm_apply ⟨x,hx⟩))

/-- Every compatible automorphism of the entire native pair extends to the
native group. This includes the full common Borel, not just the Sylow subgroup. -/
theorem restriction_surjective {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    Function.Surjective (SourceNormalizerExtension.restriction (F := F)) := by
  intro a
  obtain ⟨f,hl,hr⟩ := native_amalgam_automorphism hF hn a
  let u : SourceNormalizerExtension.flagAutomorphisms F :=
    ⟨f, map_eq_of_marked pointParabolic f a.left hl,
      map_eq_of_marked planeParabolic f a.right hr⟩
  refine ⟨u, ?_⟩
  apply RankTwoAmalgam.Iso.ext
  · ext x : 1
    exact Subtype.ext (hl x)
  · ext x : 1
    apply Subtype.ext
    change f x.val = (a.middle x).val
    exact (hl ((SourceNormalizerExtension.diagram F).left x)).trans
      (congrArg Subtype.val (a.left_commutes x))
  · ext x : 1
    exact Subtype.ext (hr x)

/-- The same extension theorem with the two actual endpoint maps reversed. -/
theorem reverseRestriction_surjective {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    Function.Surjective (SourceNormalizerExtension.reverseRestriction (F := F)) := by
  intro a
  obtain ⟨f,hf⟩ := restriction_surjective hF hn a.reverse
  exact ⟨f, congrArg (fun e => e.reverse) hf⟩

/-- Generation supplies uniqueness and multiplicative coherence of the lifts. -/
theorem unique_native_lift {D : Type*} [Group D] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (ρ : D →* RankTwoAmalgam.Iso (SourceNormalizerExtension.diagram F)
      (SourceNormalizerExtension.diagram F)) :
    ∃! σ : D →* SourceNormalizerExtension.flagAutomorphisms F,
      SourceNormalizerExtension.restriction.comp σ = ρ :=
  SourceNormalizerExtension.existsUnique_lift ρ (fun g => restriction_surjective hF hn (ρ g))

/-- Coherent lifts in the reversed orientation. -/
theorem unique_native_lift_reverse {D : Type*} [Group D] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (ρ : D →* RankTwoAmalgam.Iso (SourceNormalizerExtension.diagram F).reverse
      (SourceNormalizerExtension.diagram F).reverse) :
    ∃! σ : D →* SourceNormalizerExtension.flagAutomorphisms F,
      SourceNormalizerExtension.reverseRestriction.comp σ = ρ :=
  SourceNormalizerExtension.existsUnique_reverse_lift ρ
    (fun g => reverseRestriction_surjective hF hn (ρ g))

end CFSG.Quasithin.Chapter5.Section03SymplecticSource
