module
public import Theory.Representation.BinaryPermutation.SevenNormalizer
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# Extending a marked natural A₇ action to its ambient normalizer

An ambient action normalizing a marked natural A₇ image acts through S₇.
The action homomorphism keeps its literal kernel and original A₇ marking;
faithfulness of the ambient group and a two-core kernel are not required.

Source: Aschbacher--Smith B.3 and C.1.24, pp.83--84 and 130--131.
-/

public noncomputable section
namespace BinaryPermutation.SevenAmbientAction
open Subgroup Representation Representation.BinaryOffender

private abbrev Space := core (Fin 7)
private abbrev Actor := alternatingGroup (Fin 7)
private abbrev Full := Equiv.Perm (Fin 7)
private abbrev action := alternatingCoreRepresentation (Ω := Fin 7)

private theorem core_faithful : Function.Injective (coreRepresentation (Fin 7)) := by
  intro g h he
  apply naturalRepresentation_injective (Fin 7) (by decide)
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (coreEquivNatural (Fin 7) (by decide)).surjective v
  rw [←coreEquivNatural_equivariant,←coreEquivNatural_equivariant]
  exact congrArg (coreEquivNatural (Fin 7) (by decide)) (LinearMap.congr_fun he w)

private theorem faithful : Function.Injective action := by
  intro g h he
  apply Subtype.ext
  exact core_faithful he

private def automorphism : linearNormalizer action →* MulAut Actor :=
  let hf : Function.Injective action.asGroupHom := fun _ _ h => faithful (congrArg Units.val h)
  let e : Actor ≃* actionImage action := MonoidHom.ofInjective hf
  (MulAut.congr e.symm).toMonoidHom.comp (actionImage action).normalizerMonoidHom

private theorem intertwines (t : linearNormalizer action) (g : Actor) (v : Space) :
    t.val.val (action g v) = action (automorphism t g) (t.val.val v) := by
  let hf : Function.Injective action.asGroupHom := fun _ _ h => faithful (congrArg Units.val h)
  let e : Actor ≃* actionImage action := MonoidHom.ofInjective hf
  have he : action.asGroupHom (automorphism t g) = t.val * action.asGroupHom g * t.val⁻¹ := by
    change (e (e.symm ((actionImage action).normalizerMonoidHom t (e g)))).val = _
    rw [e.apply_symm_apply]
    rfl
  have hh := congrArg (fun u : (Module.End (ZMod 2) Space)ˣ => u.val (t.val.val v)) he
  have hinv : (t.val⁻¹).val (t.val.val v) = v := by
    change (t.val⁻¹ * t.val).val v = v
    rw [inv_mul_cancel]
    rfl
  change action (automorphism t g) (t.val.val v) =
    t.val.val (action g ((t.val⁻¹).val (t.val.val v))) at hh
  rw [hinv] at hh
  exact hh.symm

private theorem exists_permutation (t : linearNormalizer action) :
    ∃ g : Full, ∀ v : Space, t.val.val v = coreRepresentation (Fin 7) g v := by
  exact ⟨SevenNormalizer.permutationOfAut (automorphism t),
    SevenNormalizer.intertwiner
      (LinearMap.GeneralLinearGroup.toLinearEquiv t.val) (automorphism t)
      (intertwines t)⟩

/-- Permutation operators normalize the actual alternating image. -/
private def embedding : Full →* linearNormalizer action :=
  (coreRepresentation (Fin 7)).asGroupHom.codRestrict _ (fun g =>
    actionImage_le_linearNormalizer (coreRepresentation (Fin 7)) Actor ⟨g,rfl⟩)

private theorem embedding_bijective : Function.Bijective embedding := by
  constructor
  · intro g h he
    exact core_faithful
      (congrArg (fun t : linearNormalizer action => t.val.val) he)
  · intro t
    obtain ⟨g,hg⟩ := exists_permutation t
    exact ⟨g, Subtype.ext (Units.ext (LinearMap.ext (fun v => (hg v).symm)))⟩

/-- The full linear normalizer is S₇, with its literal natural action. -/
private def equiv : Full ≃* linearNormalizer action :=
  MulEquiv.ofBijective embedding embedding_bijective

/-- An ambient action extending a marked normal A₇ action has a canonical
permutation realization. No faithfulness hypothesis is needed to construct it. -/
theorem exists_ambient_hom {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (H : Subgroup G) [H.Normal] (e : H →* alternatingGroup (Fin 7)) (he : Function.Surjective e)
    (E : W ≃ₗ[ZMod 2] core (Fin 7))
    (hE : ∀ (h : H) v, E (ρ h v) = alternatingCoreRepresentation (Fin 7) (e h) (E v)) :
    ∃ f : G →* Equiv.Perm (Fin 7),
      (∀ h : H, f h = (e h).val) ∧
      (∀ g v, E (ρ g v) = coreRepresentation (Fin 7) (f g) (E v)) ∧
      f.ker = ρ.ker := by
  let τ : Representation (ZMod 2) G Space := E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (h : H) : τ h = action (e h) := by
    apply LinearMap.ext
    intro v
    change E (ρ h (E.symm v)) = action (e h) v
    rw [hE, E.apply_symm_apply]
  have hi : actionImage (τ.comp H.subtype) = actionImage action := by
    apply le_antisymm
    · rintro _ ⟨h,rfl⟩
      refine ⟨e h, Units.ext (hτ h).symm⟩
    · rintro _ ⟨h,rfl⟩
      obtain ⟨h,rfl⟩ := he h
      refine ⟨h, ?_⟩
      apply Units.ext
      exact hτ h
  let k : G →* linearNormalizer action := τ.asGroupHom.codRestrict _ (fun g => by
    change τ.asGroupHom g ∈ normalizer (actionImage action : Set _)
    rw [← hi]
    exact actionImage_le_linearNormalizer τ H ⟨g,rfl⟩)
  let f := equiv.symm.toMonoidHom.comp k
  have hf (g : G) : equiv (f g) = k g := equiv.apply_symm_apply (k g)
  have heq (g : G) (v : W) :
      E (ρ g v) = coreRepresentation (Fin 7) (f g) (E v) := by
    have hh := congrArg (fun t : linearNormalizer action => t.val.val (E v)) (hf g)
    change coreRepresentation (Fin 7) (f g) (E v) = E (ρ g (E.symm (E v))) at hh
    simpa only [E.symm_apply_apply] using hh.symm
  refine ⟨f, ?_, heq, ?_⟩
  · intro h
    apply core_faithful
    apply LinearMap.ext
    intro v
    obtain ⟨v,rfl⟩ := E.surjective v
    exact (heq h v).symm.trans (hE h v)
  · ext g
    change f g = 1 ↔ ρ g = 1
    constructor
    · intro hg
      apply LinearMap.ext
      intro v
      apply E.injective
      rw [heq, hg, map_one]
      rfl
    · intro hg
      apply core_faithful
      apply LinearMap.ext
      intro v
      obtain ⟨v,rfl⟩ := E.surjective v
      rw [← heq, hg, map_one]
      rfl

end BinaryPermutation.SevenAmbientAction
