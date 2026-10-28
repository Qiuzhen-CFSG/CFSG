module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel.LocalAction
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers
public import Theory.GroupTheory.PPerfectHom

/-!
# Triviality of the mixed action on PSL₂(4)

Transport the actual component to A₅, and then its automorphism action to
S₅ through the conjugation isomorphism. An automorphism fixing the marked
nonidentity involution lies in its permutation centralizer, a two-group
of order eight. The original block is two-perfect, so its image vanishes.
This proves the full mixed action, without first placing the block in X.

Source: Aschbacher–Smith, E.6.8 and E.6.23, printed pp.247–248 and 254;
the A₅ automorphism calculation is GLS3, Theorem 5.2.1.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel

private theorem action_eq_one_of_equiv_five
    {D X : Type*} [Group D] [Group X]
    (hD : IsPPerfect 2 D) (e : X ≃* alternatingGroup (Fin 5))
    (ρ : D →* MulAut X) (t : X) (ht : t ∉ center X) (ht2 : t ^ 2 = 1)
    (hfix : ∀ d : D, ρ d t = t) : ρ = 1 := by
  let eAut : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  let β := (MulAut.congr e).toMonoidHom.comp ρ
  let f := eAut.symm.toMonoidHom.comp β
  have horder : orderOf (e t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ht2, map_one]
    · intro he
      have ht1 : t = 1 := e.injective (he.trans (map_one e).symm)
      exact ht (ht1 ▸ (center X).one_mem)
  let C := centralizer ({(e t : Equiv.Perm (Fin 5))} : Set (Equiv.Perm (Fin 5)))
  have hp : IsPGroup 2 C := by
    apply IsPGroup.of_card_dvd_pow (n := 3)
    rw [Equiv.Perm.nat_card_centralizer,
      alternatingGroup.involution_cycleType_of_degree_le_six (by decide) (e t) horder]
    norm_num
  have hf (d : D) : f d ∈ C := by
    have he : eAut (f d) (e t) = e t := by
      change eAut (eAut.symm _) (e t) = e t
      rw [eAut.apply_symm_apply]
      change e (ρ d (e.symm (e t))) = e t
      rw [e.symm_apply_apply, hfix]
    have he' := congrArg Subtype.val he
    change f d * (e t : Equiv.Perm (Fin 5)) * (f d)⁻¹ = e t at he'
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he')
  let f' : D →* C := f.codRestrict C hf
  have htr := hD.hom_eq_one_of_isPGroup hp f'
  apply MonoidHom.ext
  intro d
  apply (MulAut.congr e).injective
  apply eAut.symm.injective
  have he := congrArg (fun a : D →* C => (a d : Equiv.Perm (Fin 5))) htr
  change f d = 1 at he
  simpa only [f, β, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MonoidHom.one_apply, map_one] using he

/-- Every marked A₃ action on the actual PSL₂(4) component is trivial.
The subnormal and inner-Sylow hypotheses of the uniform contract are
unneeded for this smallest model. -/
theorem linearTwo_fixedSylowActionTrivial {X : Type*} [Group X]
    (hm : ClassicalGroup.IsPSL X 2 4) : FixedSylowActionTrivial X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨e4⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  intro H D _ _ _ _ hD ι _ _ ρ S _ t ht ht2 hfix
  exact action_eq_one_of_equiv_five hD.2.1.twoPerfect (e.trans e4)
    (ρ.comp ι) t ht ht2 (fun d => hfix (ι d))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel
