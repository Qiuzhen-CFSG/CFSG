module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.Action
/-!
# The original exchange actor in component coordinates

The second component is marked using conjugation by the inverse of the original
source element s. Consequently conjugation by s carries its marked element
back to the original element of the first component. The resulting action
cannot preserve the factors: that would make every element of the nontrivial
component trivial. The automorphism normal form for a centerless quasisimple
square therefore gives the exchanged-factor form.

This proves the exchange-action input for the paired recognition in
Aschbacher–Smith, Lemma 2.4.34, printed p.548, with the original source element;
no assumption that s is an involution is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
variable {G : Type*} [Group G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G}
/-- The original source exchange actor has the swapped automorphism form in the
chosen, literally marked component coordinates. -/
theorem source_s_action_swapped
    (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (K : Subgroup G) (hK : IsComponentIn K (centralizer ({g.z₂} : Set G)))
    (eK : K ≃* Matrix.PSL3Two.SL) :
    let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
    let J := K ⊔ Ks
    let I := J ⊔ (T : Subgroup G)
    let eS := K.equivMapOfInjective (MulAut.conj c.s⁻¹).toMonoidHom
      (MulAut.conj c.s⁻¹).injective
    ∀ (eJ : J ≃* Matrix.PSL3Two.SL × Matrix.PSL3Two.SL)
      (_hleft : ∀ k : K, eJ (inclusion le_sup_left k) = (eK k,1))
      (_hright : ∀ k : K, eJ (inclusion le_sup_right (eS k)) = (1,eK k))
      (hn : I ≤ normalizer (J : Set G)),
    let ρ := (MulAut.congr eJ).toMonoidHom.comp
      (J.normalizerMonoidHom.comp (inclusion hn))
    let sI : I := ⟨c.s,Subgroup.mem_sup_right (c.original.T_le c.s_mem)⟩
    ∃ a b : MulAut Matrix.PSL3Two.SL,
      ρ sI = a.prodCongr b * (MulEquiv.prodComm :
        MulAut (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL)) := by
  intro Ks J I eS eJ hleft hright hn ρ sI
  let := hK.quasisimple
  let : IsQuasisimple Matrix.PSL3Two.SL := IsQuasisimple.of_mulEquiv eK
  have hact (k : K) : ρ sI (1,eK k) = (eK k,1) := by
    rw [← hright k]
    change eJ ((J.normalizerMonoidHom (inclusion hn sI))
      (eJ.symm (eJ (inclusion le_sup_right (eS k))))) = (eK k,1)
    rw [eJ.symm_apply_apply, ← hleft k]
    apply congrArg eJ
    apply Subtype.ext
    change c.s * (c.s⁻¹ * (k : G) * (c.s⁻¹)⁻¹) * c.s⁻¹ = (k : G)
    group
  rcases AutomorphismSquare.normal_form Matrix.PSL3Two.center_eq_bot (ρ sI) with
    ⟨a,b,hab⟩ | hswap
  · exfalso
    apply hK.ne_bot
    apply eq_bot_iff.mpr
    intro k hk
    have he := congrArg Prod.fst (hact ⟨k,hk⟩)
    rw [hab] at he
    change a 1 = eK ⟨k,hk⟩ at he
    rw [map_one] at he
    have he' : (⟨k,hk⟩ : K) = 1 := eK.injective (he.symm.trans eK.map_one.symm)
    exact congrArg Subtype.val he'
  · exact hswap
end CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
