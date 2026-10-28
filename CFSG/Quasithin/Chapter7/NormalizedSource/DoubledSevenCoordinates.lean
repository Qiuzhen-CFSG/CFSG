module

public import Theory.Representation.BinaryAlternatingSevenControl.FixedLine
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Alternating.Aut
public import Theory.GroupTheory.QuasithinBasic

/-!
# The faithful normalizer of an inequivalent A₇ pair

The fixed line of a Sylow two-subgroup and transitivity on nonzero vectors
make the invertible commutant of each faithful binary four-space trivial.
Schur's lemma kills the off-diagonal maps between inequivalent four-spaces.
Consequently the full linear normalizer of their direct sum embeds in
Aut(A₇) = S₇, and has two-rank at most three.

These results apply to the original conjugator-twisted constituents; they
do not assume a marking of the full ambient automizer. The chosen-module
application is in `NonFFSourceDoubledSevenCoordinates`.
Source: Aschbacher--Smith D.3.10, H.8 and 7.5.5, printed pp.201,389,701.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open Representation.BinaryAlternatingSevenControl

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- Every faithful binary A₇ four-space is irreducible, by its nonzero orbit. -/
theorem doubledSeven_four_irreducible
    (σ : Representation (ZMod 2) A7 U) (hσ : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) U = 4) : IsIrreducible σ := by
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) U)
  refine ⟨fun N => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have hn : N.toSubmodule ≠ ⊥ := fun he => hN (Subrepresentation.toSubmodule_injective he)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · exact hw ▸ N.toSubmodule.zero_mem
  obtain ⟨g,rfl⟩ := transitive σ hσ hd hv0 hw
  exact N.apply_mem_toSubmodule g hv

/-- An invertible operator commuting with a faithful A₇ four-space fixes its
unique Sylow-fixed nonzero vector and hence the entire nonzero orbit. -/
theorem doubledSeven_four_centralizer
    (σ : Representation (ZMod 2) A7 U) (hσ : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) U = 4)
    (f : U ≃ₗ[ZMod 2] U) (hf : ∀ g v, f (σ g v) = σ g (f v)) :
    f = LinearEquiv.refl _ _ := by
  let R : Sylow 2 A7 := Classical.choice inferInstance
  obtain ⟨v,hv,hfix,hunique⟩ := sylow_fixed_line σ hσ hd R
  have hfv : f v = v := (hunique (f v) (fun g => by
    change σ (g : A7) (f v) = f v
    exact (hf g v).symm.trans (congrArg f (hfix g)))).resolve_left
      (fun hz => hv (f.map_eq_zero_iff.mp hz))
  apply LinearEquiv.ext
  intro w
  by_cases hw : w = 0
  · simpa only [hw, LinearEquiv.refl_apply] using f.map_zero
  obtain ⟨g,rfl⟩ := transitive σ hσ hd hv hw
  simp only [LinearEquiv.refl_apply, hf, hfv]

private theorem four_scalar
    (σ : Representation (ZMod 2) A7 U) (hσ : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) U = 4) (f : σ.IntertwiningMap σ) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  let := doubledSeven_four_irreducible σ hσ hd
  rcases IsIrreducible.bijective_or_eq_zero f with hb | hz
  · have he := doubledSeven_four_centralizer σ hσ hd (f.ofBijective hb).toLinearEquiv
      (fun g v => LinearMap.congr_fun (f.isIntertwining' g) v)
    refine ⟨1,fun v => ?_⟩
    simpa using LinearEquiv.congr_fun he v
  · exact ⟨0,fun v => by simp [hz]⟩

private theorem cross_zero
    (σ τ : Representation (ZMod 2) A7 U)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hd : Module.finrank (ZMod 2) U = 4)
    (hne : ¬ Nonempty (σ.Equiv τ)) (f : σ.IntertwiningMap τ) : f = 0 := by
  let := doubledSeven_four_irreducible σ hσ hd
  let := doubledSeven_four_irreducible τ hτ hd
  exact (IsIrreducible.bijective_or_eq_zero f).resolve_left
    (fun hb => hne ⟨f.ofBijective hb⟩)

/-- The actual pair of inequivalent four-spaces has trivial invertible commutant. -/
theorem doubledSeven_pair_centralizer
    (σ τ : Representation (ZMod 2) A7 U)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hd : Module.finrank (ZMod 2) U = 4) (hne : ¬ Nonempty (σ.Equiv τ))
    (f : (U × U) ≃ₗ[ZMod 2] (U × U))
    (hf : ∀ g v, f ((σ.prod τ) g v) = (σ.prod τ) g (f v)) :
    f = LinearEquiv.refl _ _ := by
  let f₁₁ : σ.IntertwiningMap σ := {
    toLinearMap := (LinearMap.fst _ _ _).comp (f.toLinearMap.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro g
      ext v
      simpa using congrArg Prod.fst (hf g (v,0)) }
  let f₁₂ : τ.IntertwiningMap σ := {
    toLinearMap := (LinearMap.fst _ _ _).comp (f.toLinearMap.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro g
      ext v
      simpa using congrArg Prod.fst (hf g (0,v)) }
  let f₂₁ : σ.IntertwiningMap τ := {
    toLinearMap := (LinearMap.snd _ _ _).comp (f.toLinearMap.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro g
      ext v
      simpa using congrArg Prod.snd (hf g (v,0)) }
  let f₂₂ : τ.IntertwiningMap τ := {
    toLinearMap := (LinearMap.snd _ _ _).comp (f.toLinearMap.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro g
      ext v
      simpa using congrArg Prod.snd (hf g (0,v)) }
  obtain ⟨a,ha⟩ := four_scalar σ hσ hd f₁₁
  obtain ⟨b,hb⟩ := four_scalar τ hτ hd f₂₂
  have h₁₂ := cross_zero τ σ hτ hσ hd (fun ⟨e⟩ => hne ⟨e.symm⟩) f₁₂
  have h₂₁ := cross_zero σ τ hσ hτ hd hne f₂₁
  have hab (v : U × U) : f v = (a • v.1,b • v.2) := by
    have hs : f v = f (v.1,0) + f (0,v.2) := by rw [← map_add]; simp
    rw [hs]
    apply Prod.ext
    · change f₁₁ v.1 + f₁₂ v.2 = a • v.1
      rw [ha,h₁₂]
      simp
    · change f₂₁ v.1 + f₂₂ v.2 = b • v.2
      rw [hb,h₂₁]
      simp
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) U)
  obtain ⟨v,hv⟩ := exists_ne (0 : U)
  have ha0 : a ≠ 0 := by
    intro hz
    have he : f (v,0) = f 0 := by rw [hab,hab,hz]; simp
    exact hv (congrArg Prod.fst (f.injective he))
  have hb0 : b ≠ 0 := by
    intro hz
    have he : f (0,v) = f 0 := by rw [hab,hab,hz]; simp
    exact hv (congrArg Prod.snd (f.injective he))
  have bit : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  ext v : 1
  simp only [hab,bit a ha0,bit b hb0,one_smul,Prod.mk.eta,LinearEquiv.refl_apply]

/-- The full linear normalizer, including all outer operators, has two-rank at most three. -/
theorem doubledSeven_normalizer_rank
    (σ τ : Representation (ZMod 2) A7 U)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hd : Module.finrank (ZMod 2) U = 4) (hne : ¬ Nonempty (σ.Equiv τ)) :
    primeRank 2 (linearNormalizer (σ.prod τ)) ≤ 3 := by
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
      have hc := (mul_inv_eq_iff_eq_mul).mp hh
      exact congrArg (fun z : (Module.End (ZMod 2) (U × U))ˣ => z.val v) hc
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
  let : Finite U := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) (U × U)) := Finite.of_injective
    (fun f : Module.End (ZMod 2) (U × U) => (f : U × U → U × U)) DFunLike.coe_injective
  have hr := primeRank_le_of_injective 2 f hf
  rw [← primeRank_equiv 2 (MulAut.congr e),primeRank_equiv 2 c.symm] at hr
  exact hr.trans Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_symmetric.le

/-- A faithful ambient action with the marked pair as a normal component
inherits the bound from its full linear normalizer. -/
theorem doubledSeven_rank_of_marked_normal_range
    {H J X : Type*} [Group H] [Group J] [Finite H]
    [AddCommGroup X] [Module (ZMod 2) X]
    (σ τ : Representation (ZMod 2) A7 U)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hd : Module.finrank (ZMod 2) U = 4) (hne : ¬ Nonempty (σ.Equiv τ))
    (ρ : Representation (ZMod 2) H X) (hρ : Function.Injective ρ)
    (i : J →* H) [i.range.Normal]
    (q : J →* A7) (hq : Function.Surjective q)
    (E : X ≃ₗ[ZMod 2] (U × U))
    (hE : ∀ j v, E (ρ (i j) v) = (σ.prod τ) (q j) (E v)) :
    primeRank 2 H ≤ 3 := by
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
  let : Finite U := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) (U × U)) := Finite.of_injective
    (fun f : Module.End (ZMod 2) (U × U) => (f : U × U → U × U)) DFunLike.coe_injective
  exact (primeRank_le_of_injective 2 j hj).trans
    (doubledSeven_normalizer_rank σ τ hσ hτ hd hne)

end CFSG.Quasithin.Chapter7.NormalizedSource
