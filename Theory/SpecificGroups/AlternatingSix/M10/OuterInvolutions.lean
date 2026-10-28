module
public import Theory.SpecificGroups.AlternatingSix.M10.InvolutionAlignment
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed

/-!
# The two M10 orbits of outer involutions in Aut(A6)

Natural outer involutions are transpositions or triple transpositions; the
exceptional symmetric-group automorphism exchanges these two permutation
classes. The existing exceptional-involution certificate conjugates every
involution outside the natural S6 to its canonical representative. Finally,
an arbitrary conjugator between involutions outside the index-two M10 is
corrected into M10 by multiplication with the target involution.

Source: Aschbacher–Smith J.2.7(4,7), printed p.436 (PDF p.447), using GLS3 5.2.7.
-/

open Subgroup
namespace AlternatingSix.M10.OuterInvolutions
open ShadowLocal GLS3.Chapter5 Equiv.Perm

lemma natural_conjugate_transposition (β : AutA6) (hβ : orderOf β=2)
    (hn : β∈natural) (hM : β∉extension) :
    IsConj β Identification.transposition := by
  obtain ⟨σ,hσ⟩ := hn
  change permutationAction σ=β at hσ
  subst β
  have hs2 : orderOf σ=2 :=
    (orderOf_injective permutationAction permutationAction_injective σ).symm.trans hβ
  have hsodd : σ∉alternatingGroup (Fin 6) := by
    intro he
    exact hM (Action.permutationAction_mem_extension_iff σ |>.mpr he)
  have hf : (Equiv.swap (4:Fin 6) 5).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr (by decide)
  rcases odd_involution_cycleType σ hs2 hsodd with hs | hs
  · exact permutationAction.map_isConj (isConj_of_cycleType_eq
      ((isSwap_iff_cycleType.mp hs).trans (isSwap_iff_cycleType.mp hf).symm))
  · have hσf : IsConj σ (outerHom (Equiv.swap (4:Fin 6) 5)) :=
      isConj_of_cycleType_eq (hs.trans outerHom_standardSwap_cycleType.symm)
    have hout : IsConj Identification.transposition
        (permutationAction (outerHom (Equiv.swap (4:Fin 6) 5))) := by
      apply isConj_iff.mpr
      refine ⟨outerAltAut,?_⟩
      apply mul_inv_eq_iff_eq_mul.mpr
      apply MulEquiv.ext
      intro g
      apply Subtype.ext
      change outerHom ((Equiv.swap (4:Fin 6) 5)*g.val*(Equiv.swap (4:Fin 6) 5)⁻¹)=
        outerHom (Equiv.swap (4:Fin 6) 5)*outerHom g.val*(outerHom (Equiv.swap (4:Fin 6) 5))⁻¹
      simp only [map_mul,map_inv]
    exact (permutationAction.map_isConj hσf).trans hout.symm

lemma exceptional_conjugate_canonical (β : AutA6) (hβ : orderOf β=2)
    (hn : β∉natural) : IsConj canonicalExceptionalAut β := by
  obtain ⟨σ,hσ⟩ := exceptionalAut_eq_twist β hn
  have hs2 : exceptionalTwistAut σ^2=1 := by
    rw [←hσ,←hβ,pow_orderOf_eq_one]
  obtain ⟨τ,hτ⟩ := exceptionalTwistAut_conjugate_canonical σ hs2
  apply isConj_iff.mpr
  exact ⟨permutationAction τ,(hσ.trans hτ).symm⟩

lemma conjugator_in_extension (β γ : AutA6) (hγ : γ∉extension)
    (h : IsConj β γ) : ∃a∈extension,a*β*a⁻¹=γ := by
  obtain ⟨a,ha⟩ := isConj_iff.mp h
  by_cases ham : a∈extension
  · exact ⟨a,ham,ha⟩
  · refine ⟨γ*a,?_,?_⟩
    · rw [extension.mul_mem_iff_of_index_two Action.extension_index]
      exact iff_of_false hγ ham
    · calc
        (γ*a)*β*(γ*a)⁻¹=γ*(a*β*a⁻¹)*γ⁻¹ := by group
        _=γ := by rw [ha];group

public theorem same_side_conjugate (β γ : AutA6) (hβ : orderOf β=2) (hγ : orderOf γ=2)
    (hβM : β∉extension) (hγM : γ∉extension)
    (hs : β∈natural ↔ γ∈natural) : ∃a∈extension,a*β*a⁻¹=γ := by
  apply conjugator_in_extension β γ hγM
  by_cases hβn : β∈natural
  · exact (natural_conjugate_transposition β hβ hβn hβM).trans
      (natural_conjugate_transposition γ hγ (hs.mp hβn) hγM).symm
  · exact (exceptional_conjugate_canonical β hβ hβn).symm.trans
      (exceptional_conjugate_canonical γ hγ (fun h => hβn (hs.mpr h)))

end AlternatingSix.M10.OuterInvolutions
