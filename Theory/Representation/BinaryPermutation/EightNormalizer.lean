module
public import Theory.Representation.BinaryPermutation.EightCommutant
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.SpecificGroups.SymmetricEight.InvolutionActions

/-!
# The full linear normalizer of the binary orthogonal six-space

Conjugation on A₈ identifies every normalizing operator with a permutation
of eight letters, up to an operator centralizing A₈. The natural module's
trivial linear centralizer removes this discrepancy. The resulting
identification extends an actual normal A₈ action, preserving its original
coordinates and all ambient actors.

Source: Aschbacher--Smith, B.3.1--2 and the orthogonal row in 15.2.23(c),
printed pp.83--84 and 1117.
-/

public noncomputable section
namespace BinaryPermutation.EightNormalizer
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricEight.Involutions

abbrev Space := natural (Fin 8)
abbrev Actor := alternatingGroup (Fin 8)
abbrev Full := Equiv.Perm (Fin 8)
abbrev action := alternatingNaturalRepresentation (Ω := Fin 8)

private theorem faithful : Function.Injective action := by
  intro g h he
  apply Subtype.ext
  exact naturalRepresentation_injective (Fin 8) (by decide) he

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

/-- Every normalizing operator is an actual permutation operator. -/
theorem exists_permutation (t : linearNormalizer action) :
    ∃ g : Full, ∀ v : Space, t.val.val v = naturalRepresentation (Fin 8) g v := by
  let τ := naturalRepresentation (Fin 8)
  obtain ⟨g,hg⟩ := permutationAutEquiv.surjective (automorphism t)
  let F := (LinearMap.GeneralLinearGroup.toLinearEquiv t.val).trans
    (LinearEquiv.ofBijective (τ g⁻¹) (τ.apply_bijective g⁻¹))
  have hF : ∀ k : Actor, ∀ v,
      F (τ k.val v) = τ k.val (F v) := by
    intro k v
    change τ g⁻¹ (t.val.val (action k v)) = _
    rw [intertwines, ← hg]
    change τ g⁻¹ (τ (g * k.val * g⁻¹) (t.val.val v)) =
      τ k.val (τ g⁻¹ (t.val.val v))
    have he : g⁻¹ * (g * k.val * g⁻¹) = k.val * g⁻¹ := by group
    calc
      _ = τ (g⁻¹ * (g * k.val * g⁻¹)) (t.val.val v) :=
        (LinearMap.congr_fun (map_mul τ _ _) _).symm
      _ = τ (k.val * g⁻¹) (t.val.val v) := by rw [he]
      _ = _ := LinearMap.congr_fun (map_mul τ _ _) _
  have he := EightCommutant.commuting_eq_refl F hF
  refine ⟨g, fun v => ?_⟩
  have hv := congrArg (fun f : Space ≃ₗ[ZMod 2] Space => f v) he
  change τ g⁻¹ (t.val.val v) = v at hv
  have hh := congrArg (τ g) hv
  have hc (w : Space) : τ g (τ g⁻¹ w) = w := by
    change (τ g * τ g⁻¹) w = w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  exact (hc _).symm.trans hh

/-- Permutation operators normalize the actual alternating image. -/
def embedding : Full →* linearNormalizer action :=
  (naturalRepresentation (Fin 8)).asGroupHom.codRestrict _ (fun g =>
    actionImage_le_linearNormalizer (naturalRepresentation (Fin 8)) Actor ⟨g,rfl⟩)

theorem embedding_bijective : Function.Bijective embedding := by
  constructor
  · intro g h he
    exact naturalRepresentation_injective (Fin 8) (by decide)
      (congrArg (fun t : linearNormalizer action => t.val.val) he)
  · intro t
    obtain ⟨g,hg⟩ := exists_permutation t
    exact ⟨g, Subtype.ext (Units.ext (LinearMap.ext (fun v => (hg v).symm)))⟩

/-- The full linear normalizer is S₈, with its literal natural action. -/
def equiv : Full ≃* linearNormalizer action :=
  MulEquiv.ofBijective embedding embedding_bijective

/-- An ambient action extending a marked normal A₈ action has a canonical
permutation realization. No faithfulness hypothesis is needed to construct it. -/
theorem exists_ambient_hom {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (H : Subgroup G) [H.Normal] (e : H →* Actor) (he : Function.Surjective e)
    (E : W ≃ₗ[ZMod 2] Space)
    (hE : ∀ (h : H) v, E (ρ h v) = action (e h) (E v)) :
    ∃ f : G →* Full,
      (∀ h : H, f h = (e h).val) ∧
      (∀ g v, E (ρ g v) = naturalRepresentation (Fin 8) (f g) (E v)) ∧
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
      E (ρ g v) = naturalRepresentation (Fin 8) (f g) (E v) := by
    have hh := congrArg (fun t : linearNormalizer action => t.val.val (E v)) (hf g)
    change naturalRepresentation (Fin 8) (f g) (E v) = E (ρ g (E.symm (E v))) at hh
    simpa only [E.symm_apply_apply] using hh.symm
  refine ⟨f, ?_, heq, ?_⟩
  · intro h
    apply naturalRepresentation_injective (Fin 8) (by decide)
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
      apply naturalRepresentation_injective (Fin 8) (by decide)
      apply LinearMap.ext
      intro v
      obtain ⟨v,rfl⟩ := E.surjective v
      rw [← heq, hg, map_one]
      rfl

end BinaryPermutation.EightNormalizer
