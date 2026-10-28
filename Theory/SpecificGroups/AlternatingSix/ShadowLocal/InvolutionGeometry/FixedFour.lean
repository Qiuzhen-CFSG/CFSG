module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed

/-!
# Alternating four-subgroups fixed by the outer permutation actions

The transposition action on A₆ fixes a copy of S₄, hence A₄. The triple
transposition action on A₇ is transported from the corresponding six-letter
action by adjoining its one fixed point. Conjugacy by cycle type retains
the prescribed permutation in both embeddings.

Application: the alternating alternatives of Aschbacher--Smith 1.1.5(3),
as inspected in 14.3.22, printed p.999.
-/

public section
open Subgroup Equiv Equiv.Perm GLS3.Chapter5
namespace AlternatingSix.ShadowLocal

theorem swap_fixed_alternatingFour_embedding (σ : Perm (Fin 6)) (hσ : σ.IsSwap) :
    ∃ f : alternatingGroup (Fin 4) →* alternatingGroup (Fin 6),
      Function.Injective f ∧ ∀ x, σ * (f x : Perm (Fin 6)) * σ⁻¹ = f x := by
  let e := swapFixedEquiv σ hσ
  let k := e.symm.toMonoidHom.comp (alternatingGroup (Fin 4)).subtype
  let f := (automorphismFixedSubgroup (permutationAction σ)).subtype.comp k
  refine ⟨f, Subtype.val_injective.comp (e.symm.injective.comp Subtype.val_injective), ?_⟩
  intro x
  exact congrArg Subtype.val (k x).property

private def extendSix : Perm (Fin 6) →* Perm (Fin 7) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7)).toMonoidHom.comp
    ((sumCongrHom (Fin 6) (Fin 1)).comp
      ((MonoidHom.id (Perm (Fin 6))).prod (1 : Perm (Fin 6) →* Perm (Fin 1))))

private theorem extendSix_injective : Function.Injective extendSix := by
  intro σ τ h
  have hp := (Equiv.permCongrHom finSumFinEquiv).injective h
  have hq := sumCongrHom_injective hp
  exact congrArg Prod.fst hq

private theorem extendSix_even (x : alternatingGroup (Fin 6)) :
    extendSix x ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  change sign ((finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7).permCongr
    (Equiv.sumCongr (x : Perm (Fin 6)) 1)) = 1
  rw [sign_permCongr,sign_sumCongr,mem_alternatingGroup.mp x.property,map_one,mul_one]

private def extendAlt : alternatingGroup (Fin 6) →* alternatingGroup (Fin 7) :=
  (extendSix.comp (alternatingGroup (Fin 6)).subtype).codRestrict _ extendSix_even

private theorem extendAlt_injective : Function.Injective extendAlt := by
  intro x y h
  exact Subtype.ext (extendSix_injective (congrArg Subtype.val h))

private def standardSix : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5
private theorem standardSix_type : standardSix.cycleType = {2,2,2} := by decide +kernel
private theorem standardSeven_type : (extendSix standardSix).cycleType = {2,2,2} := by decide +kernel

theorem tripleSwapSeven_fixed_alternatingFour_embedding (σ : Perm (Fin 7)) (hσ : σ.cycleType = {2,2,2}) :
    ∃ f : alternatingGroup (Fin 4) →* alternatingGroup (Fin 7),
      Function.Injective f ∧ ∀ x, σ * (f x : Perm (Fin 7)) * σ⁻¹ = f x := by
  let e := tripleSwapFixedEquiv standardSix standardSix_type
  let k := e.symm.toMonoidHom.comp (alternatingGroup (Fin 4)).subtype
  let f6 := (automorphismFixedSubgroup (permutationAction standardSix)).subtype.comp k
  let f0 := extendAlt.comp f6
  have hfixed (x : alternatingGroup (Fin 4)) :
      extendSix standardSix * (f0 x : Perm (Fin 7)) * (extendSix standardSix)⁻¹ = f0 x := by
    have hh : standardSix * (f6 x : Perm (Fin 6)) * standardSix⁻¹ = f6 x :=
      congrArg Subtype.val (k x).property
    change extendSix standardSix * extendSix (f6 x) * (extendSix standardSix)⁻¹ = extendSix (f6 x)
    simpa only [map_mul,map_inv] using congrArg extendSix hh
  have hconj : IsConj σ (extendSix standardSix) :=
    isConj_of_cycleType_eq (hσ.trans standardSeven_type.symm)
  obtain ⟨p,hp⟩ := isConj_iff.mp hconj
  let j : MulAut (alternatingGroup (Fin 7)) := MulAut.conjNormal p⁻¹
  let f := j.toMonoidHom.comp f0
  refine ⟨f, j.injective.comp (extendAlt_injective.comp
    (Subtype.val_injective.comp (e.symm.injective.comp Subtype.val_injective))), ?_⟩
  intro x
  change σ * (p⁻¹ * (f0 x : Perm (Fin 7)) * (p⁻¹)⁻¹) * σ⁻¹ =
    p⁻¹ * (f0 x : Perm (Fin 7)) * (p⁻¹)⁻¹
  rw [inv_inv]
  calc
    _ = p⁻¹ * (extendSix standardSix * (f0 x : Perm (Fin 7)) *
      (extendSix standardSix)⁻¹) * p := by rw [←hp]; group
    _ = _ := by rw [hfixed]

end AlternatingSix.ShadowLocal
