module
public import Stellmacher.SectionTwo.PushingUpThreeFive
public import Stellmacher.SectionTwo.LemmaTwoFour
public import Stellmacher.SectionTwo.LemmaTwoFiveDefs
public import Stellmacher.SectionTwo.LemmaTwoOne

/-!
# Stellmacher (2.5): the normal join of odd automorphism translates

Under the explicit characteristic-subgroup and unique-maximal-overgroup
hypotheses, with the specified SL₂(2) centralizer quotient, the join of all
V-translates by an odd-order subgroup of Aut(S) is normal in G and lies in
O₂(G). The public existential records this exact join.

The proved *Pushing up* (3.5) specialization supplies normality, using square
control and the contained-orbit argument. Each translate is the ambient image
of a subgroup of S, so their join is a two-subgroup. Its normality then places
it in the two-core by the defining normal-subgroup supremum.

Source: `refs/latex/stellmacher-n-group.tex`, (2.5), citing Stellmacher,
*Pushing up*, Arch. Math. 46 (1986), (3.5), journal p.16.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionTwo

universe u

public theorem lemma_two_five
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcharacteristic :
      ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
        ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique :
      IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q)
    (hker : q.ker = cSubgroup S)
    (hbar : Nonempty
      (barG ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))
    (T : Subgroup (MulAut S)) (hT : Odd (Nat.card T)) :
    ∃ K : Subgroup G,
      K = ⨆ τ : T, automorphismTranslateV S (τ : MulAut S) ∧
      K.Normal ∧ K ≤ pCore 2 G := by
  have hnormal := pushing_up_three_five_normal
    h S hcharacteristic hunique q hq hker hbar T hT
  let K : Subgroup G :=
    ⨆ τ : T, automorphismTranslateV S (τ : MulAut S)
  have hK_le : K ≤ (S : Subgroup G) := by
    refine iSup_le fun τ => ?_
    exact Subgroup.map_subtype_le _
  have hK_two : IsPGroup 2 ↑K := S.isPGroup'.to_le hK_le
  have hK_core : K ≤ pCore 2 G := le_sSup ⟨hnormal, hK_two⟩
  exact ⟨K, rfl, hnormal, hK_core⟩

end Stellmacher.SectionTwo
