module
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Normalizer
public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator

/-!
# Faithful ambient actors of the marked natural SL₂(4) module

A faithful binary representation whose restriction to a normal subgroup is the
literal natural SL₂(4) action embeds the entire ambient group in ΓL₂(4).
The binary-linear image of the normal subgroup is exactly the natural SL₂ image,
so normality places each ambient actor in its normalizer. The existing exact
normalizer equivalence supplies the semilinear embedding and preserves every
marked SL₂ element. Consequently its subgroup image is the determinant-one
layer, with no additional finite-image classification assumption.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
13.7.19, printed pp.944–945, using the natural normalizer identification of
6.2.5. The chapter source consumer supplies its actual faithful moved-section
representation and its natural SL₂(4) marking.
-/

public section
noncomputable section
namespace Representation.SL2FourNatural.SemilinearNormalizer
open Subgroup
variable {H : Type*} [Group H]

theorem exists_injective_ambient_action
    (K : Subgroup H) (hK : K.Normal) (e : K ≃* SL)
    (γ : Representation (ZMod 2) H V) (hγ : Function.Injective γ)
    (hres : ∀ (k : K) (v : V),
      γ (k : H) v = PointCommutator.representation (e k) v) :
    ∃ f : H →* Gamma, Function.Injective f ∧
      ∀ k : K, f (k : H) = special (e k) := by
  let a : H →* BinaryGL :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
      γ.asGroupHom
  have hainj : Function.Injective a := by
    intro x y hxy
    apply hγ
    apply LinearMap.ext
    intro v
    exact LinearEquiv.congr_fun hxy v
  have hmark (k : K) : a (k : H) = action (e k) := by
    apply LinearEquiv.ext
    intro v
    exact hres k v
  have hmap : K.map a = action.range := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨e ⟨k, hk⟩, (hmark ⟨k, hk⟩).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(e.symm k : H), (e.symm k).property, by
        rw [hmark, e.apply_symm_apply]⟩
  let : K.Normal := hK
  have hnorm : a.range ≤ normalizer := by
    rintro _ ⟨x, rfl⟩
    change a x ∈ Subgroup.normalizer (action.range : Set BinaryGL)
    rw [←hmap]
    exact K.le_normalizer_map a
      (mem_map_of_mem a (le_normalizer_of_normal (mem_top x)))
  let b : H →* normalizer := a.codRestrict normalizer (fun x => hnorm ⟨x, rfl⟩)
  let f : H →* Gamma := normalizerEquiv.symm.toMonoidHom.comp b
  refine ⟨f, normalizerEquiv.symm.injective.comp ?_, ?_⟩
  · exact (MonoidHom.injective_codRestrict a normalizer _).mpr hainj
  · intro k
    apply normalizerEquiv.injective
    apply Subtype.ext
    change (normalizerEquiv (normalizerEquiv.symm (b (k : H))) : BinaryGL) =
      (normalizerEquiv (special (e k)) : BinaryGL)
    rw [normalizerEquiv.apply_symm_apply, normalizerEquiv_apply, natural_special]
    exact hmark k

theorem marked_ambient_action_map
    (K : Subgroup H) (e : K ≃* SL) (f : H →* Gamma)
    (hmark : ∀ k : K, f (k : H) = special (e k)) :
    K.map f = special.range := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e ⟨k, hk⟩, (hmark ⟨k, hk⟩).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(e.symm k : H), (e.symm k).property, by
      rw [hmark, e.apply_symm_apply]⟩

theorem exists_injective_ambient_action_map
    (K : Subgroup H) (hK : K.Normal) (e : K ≃* SL)
    (γ : Representation (ZMod 2) H V) (hγ : Function.Injective γ)
    (hres : ∀ (k : K) (v : V),
      γ (k : H) v = PointCommutator.representation (e k) v) :
    ∃ f : H →* Gamma, Function.Injective f ∧
      (∀ k : K, f (k : H) = special (e k)) ∧ K.map f = special.range := by
  obtain ⟨f, hf, hm⟩ := exists_injective_ambient_action K hK e γ hγ hres
  exact ⟨f, hf, hm, marked_ambient_action_map K e f hm⟩

end Representation.SL2FourNatural.SemilinearNormalizer
