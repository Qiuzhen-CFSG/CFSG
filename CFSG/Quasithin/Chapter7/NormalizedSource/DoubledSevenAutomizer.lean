module

public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenCoordinates

/-!
# The compatible seven-letter action of a doubled A₇ normalizer

Conjugation on the actual normal component is faithful because the two
inequivalent four-spaces have trivial invertible commutant. The isomorphism
Aut(A₇) = S₇ supplies a seven-letter embedding. Its restriction to the
component is the original marking, not an independently chosen group tag.
The chosen-orbit consumer in NonFFSourceDoubledSevenAutomizer proves that
the original seed-exchanging element makes this embedding surjective.
Source: Aschbacher--Smith D.3.10, H.8 and 7.5.5, printed pp.201,389,701.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open Representation.BinaryAlternatingSevenControl
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- The component's actual inclusion in its linear normalizer. -/
@[expose] def doubledSevenInner (σ τ : Representation (ZMod 2) A7 U) :
    A7 →* linearNormalizer (σ.prod τ) :=
  (σ.prod τ).asGroupHom.codRestrict _
    (fun g => (actionImage (σ.prod τ)).le_normalizer ⟨g,rfl⟩)

/-- Faithful conjugation on the component, retaining the original inner action. -/
theorem doubledSeven_normalizer_embedding
    (σ τ : Representation (ZMod 2) A7 U)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hd : Module.finrank (ZMod 2) U = 4) (hne : ¬ Nonempty (σ.Equiv τ)) :
    ∃ p : linearNormalizer (σ.prod τ) →* Equiv.Perm (Fin 7),
      Function.Injective p ∧ ∀ g, p (doubledSevenInner σ τ g) = g.val := by
  let μ := σ.prod τ
  let f := (actionImage μ).normalizerMonoidHom
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    have ha' : f a = 1 := ha
    let E := LinearMap.GeneralLinearGroup.toLinearEquiv a.val
    have hE : ∀ g v, E (μ g v) = μ g (E v) := by
      intro g v
      have hh := congrArg (fun β : MulAut (actionImage μ) =>
        (β (actionHom μ g)).val) ha'
      change a.val * μ.asGroupHom g * a.val⁻¹ = μ.asGroupHom g at hh
      exact congrArg (fun z : (Module.End (ZMod 2) (U × U))ˣ => z.val v)
        ((mul_inv_eq_iff_eq_mul).mp hh)
    have hid := doubledSeven_pair_centralizer σ τ hσ hτ hd hne E hE
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact LinearEquiv.congr_fun hid v
  have hi : Function.Injective (actionHom μ) := by
    intro g h he
    apply hσ
    apply LinearMap.ext
    intro v
    exact congrArg (fun z : actionImage μ => (z.val.val (v,0)).1) he
  let e := MulEquiv.ofBijective (actionHom μ) ⟨hi,μ.asGroupHom.rangeRestrict_surjective⟩
  let c : Equiv.Perm (Fin 7) ≃* MulAut A7 := MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let p : linearNormalizer μ →* Equiv.Perm (Fin 7) :=
    c.symm.toMonoidHom.comp ((MulAut.congr e.symm).toMonoidHom.comp f)
  refine ⟨p,c.symm.injective.comp ((MulAut.congr e.symm).injective.comp hf),?_⟩
  intro g
  apply c.injective
  change c (c.symm (MulAut.congr e.symm (f (doubledSevenInner σ τ g)))) = c g.val
  rw [c.apply_symm_apply]
  apply MulEquiv.ext
  intro a
  apply e.injective
  change e (e.symm (f (doubledSevenInner σ τ g) (e a))) =
    e (MulAut.conjNormal g.val a)
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change μ.asGroupHom g * μ.asGroupHom a * (μ.asGroupHom g)⁻¹ =
    μ.asGroupHom (g * a * g⁻¹)
  simp only [map_mul,map_inv]

/-- The seven-letter map for a larger faithful actor agrees with the
surjective marking of its actual normal component. -/
theorem doubledSeven_embedding_of_marked_normal_range
    {H J X : Type*} [Group H] [Group J]
    [AddCommGroup X] [Module (ZMod 2) X]
    (σ τ : Representation (ZMod 2) A7 U)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hd : Module.finrank (ZMod 2) U = 4) (hne : ¬ Nonempty (σ.Equiv τ))
    (ρ : Representation (ZMod 2) H X) (hρ : Function.Injective ρ)
    (i : J →* H) [i.range.Normal]
    (q : J →* A7) (hq : Function.Surjective q)
    (E : X ≃ₗ[ZMod 2] (U × U))
    (hE : ∀ j v, E (ρ (i j) v) = (σ.prod τ) (q j) (E v)) :
    ∃ p : H →* Equiv.Perm (Fin 7), Function.Injective p ∧
      ∀ j, p (i j) = (q j).val := by
  let μ := σ.prod τ
  let γ : Representation (ZMod 2) H (U × U) := E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : X) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (j : J) : γ (i j) = μ (q j) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [← he]
    exact hE j v
  have himage : i.range.map γ.asGroupHom = actionImage μ := by
    ext z
    constructor
    · rintro ⟨_,⟨j,rfl⟩,rfl⟩
      exact ⟨q j,Units.ext (hres j).symm⟩
    · rintro ⟨p,rfl⟩
      obtain ⟨j,rfl⟩ := hq p
      exact ⟨i j,⟨j,rfl⟩,Units.ext (hres j)⟩
  have hn (g : H) : γ.asGroupHom g ∈ linearNormalizer μ := by
    change γ.asGroupHom g ∈ normalizer (actionImage μ : Set _)
    rw [← himage]
    exact i.range.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let j : H →* linearNormalizer μ := γ.asGroupHom.codRestrict _ hn
  have hj : Function.Injective j := by
    intro x y hxy
    exact hγ (congrArg (fun z : linearNormalizer μ => z.val.val) hxy)
  obtain ⟨p,hp,hpi⟩ := doubledSeven_normalizer_embedding σ τ hσ hτ hd hne
  refine ⟨p.comp j,hp.comp hj,?_⟩
  intro l
  have heq : j (i l) = doubledSevenInner σ τ (q l) := Subtype.ext (Units.ext (hres l))
  exact (congrArg p heq).trans (hpi (q l))

end CFSG.Quasithin.Chapter7.NormalizedSource
