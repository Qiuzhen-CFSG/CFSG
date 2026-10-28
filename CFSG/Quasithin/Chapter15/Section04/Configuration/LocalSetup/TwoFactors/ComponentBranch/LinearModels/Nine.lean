module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.SpecificGroups.AlternatingSix.SylowFixedAction

/-!
# The surviving PSL₂(9) component and its symmetric extension

Transport the given Sylow subgroup and faithful elementary four-group action
through the existing concrete PSL₂(9)–A₆ equivalence. The A₆ calculation then
identifies the generated inner extension with S₆. Both the embedded component
and the action are recorded by pointwise equations.

The PSL₂–A₆ comparison uses the licensed ATLAS construction already ported in
`Order360`: its projective-line and complementary-triple actions have the same
generator images. The argument here does not use uniqueness of a simple group
of order 360.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 15.4.18,
printed pp.1162–1163. Eliminating the other permitted field sizes remains a
separate obligation in `LinearModels`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels
open scoped MatrixGroups
open AlternatingSix.ShadowLocal

/-- The surviving field size gives actual component and extension equivalences,
with the embedded component and every automorphism's action preserved. -/
theorem exists_symmetric_extension_of_card_nine
    {F A : Type*} [Field F] [Finite F] [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hF : Nat.card F = 9) (P : Sylow 2 PSL(2,F))
    (ρ : A →* MulAut PSL(2,F)) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4)
    (hfix : ∀ a x, x ∈ (P : Subgroup PSL(2,F)) → ρ a x = x) :
    ∃ (e : PSL(2,F) ≃* alternatingGroup (Fin 6))
      (Φ : MulAut.innerExtension ρ ≃* Equiv.Perm (Fin 6)),
      (∀ x : PSL(2,F), Φ ⟨MulAut.conj x, MulAut.conj_mem_innerExtension ρ x⟩ =
        (e x : Equiv.Perm (Fin 6))) ∧
      ∀ (g : MulAut.innerExtension ρ) (x : PSL(2,F)),
        (e (g.val x) : Equiv.Perm (Fin 6)) =
          Φ g * (e x : Equiv.Perm (Fin 6)) * (Φ g)⁻¹ := by
  let e := Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF
  let ρ' := (MulAut.congr e).toMonoidHom.comp ρ
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hρ' : Function.Injective ρ' := (MulAut.congr e).injective.comp hρ
  have hf' : ∀ a x, x ∈ (P' : Subgroup A6) → ρ' a x = x := by
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change e (ρ a (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hfix a y hy]
  let Ψ := sylowFixedExtensionEquiv P' ρ' hρ' hA hf'
  let Φ := (MulAut.innerExtensionCongr e ρ).trans Ψ
  refine ⟨e, Φ, ?_, ?_⟩
  · intro x
    change Ψ (MulAut.innerExtensionCongr e ρ
      ⟨MulAut.conj x, MulAut.conj_mem_innerExtension ρ x⟩) = _
    have he : MulAut.innerExtensionCongr e ρ
        ⟨MulAut.conj x, MulAut.conj_mem_innerExtension ρ x⟩ =
        ⟨MulAut.conj (e x), MulAut.conj_mem_innerExtension ρ' (e x)⟩ := by
      apply Subtype.ext
      exact MulAut.congr_conj e x
    rw [he]
    exact sylowFixedExtensionEquiv_inner P' ρ' hρ' hA hf' (e x)
  · intro g x
    have hg := sylowFixedExtensionEquiv_action P' ρ' hρ' hA hf'
      (MulAut.innerExtensionCongr e ρ g) (e x)
    rw [MulAut.innerExtensionCongr_apply_action] at hg
    exact hg

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels
