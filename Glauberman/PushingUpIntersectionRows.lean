module
public import Glauberman.FixedNormalPairRows
public import Glauberman.PushingUpActionRecognition
public import Glauberman.PushingUpNaturalActionConsequences
public import Theory.SpecificGroups.SL2.MainHypothesisPair

/-!
# Elementary maximum intersection rows in the original Main Hypothesis

The specified Sylow automorphism and a generating conjugate give the literal
fixed-normal-free pair with intersection O₂(H). The original omega-action
recognition supplies both uniform fixed-index bounds. The proved numerical
recursion then reaches an elementary intersection which is maximum abelian
in both original Sylows. The final theorem takes only the original Main
Hypothesis, preserving the arbitrary PSL₂(4) quotient kernel K throughout.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas4.2–4.5 and the
maximum-order assertion of4.6(b), printedpp44–46. Full intersection-array
geometry and the later nilpotence-class argument remain separate results.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
open scoped IsMulCommutative
open Representation Representation.BinaryOffender
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

/-- The original twisted pair satisfies the numerical hypotheses used at
every recursive intersection row. The two source natural-action markings
remain the independent recognition inputs. -/
theorem original_numerical_pair_of_natural_quotient
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (q : H →* SL2FourNatural.SL) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (omegaCenterIn (pCore 2 H) : Set H))
    (E : (Additive (omegaCenterIn (pCore 2 H)) ⧸ fixedSpace (omegaAction H) ⊤)
      ≃ₗ[ZMod 2] SL2FourNatural.V)
    (hE : ∀ h v, E (fixedQuotient (omegaAction H) ⊤ h v) =
      specialLinearNatural 2 (q h) (E v)) :
    ∃ g : H,
      (S : Subgroup H) ⊔ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = pCore 2 H ∧
      NumericalPair (S : Subgroup H) ((S : Subgroup H).map (MulAut.conj g).toMonoidHom)
        (twistedConjugacy (S : Subgroup H) α g) := by
  obtain ⟨g,hgen,hinter,hfix⟩ := Theory.SpecificGroups.SL2.original_twisted_pair_of_psl2_four
    hF S α hu K e hno
  let T := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have huT : Order.HasUniqueMaximalOver (T : Subgroup H) ⊤ := by
    have hh := hu.map (MulAut.conj g).mapSubgroup
    rw [OrderIso.map_top] at hh
    exact hh
  have hidxS := (Theory.SpecificGroups.SL2.sylow_twoCore_quotient_elementary_four
    hF S hu K e).2
  have hidxT := (Theory.SpecificGroups.SL2.sylow_twoCore_quotient_elementary_four
    hF T huT K e).2
  refine ⟨g,hgen,hinter,S.isPGroup',hfix,?_,?_,?_,?_,?_,?_⟩
  · change _ ≤ normalizer (((S : Subgroup H) ⊓
      (S : Subgroup H).map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H)
    rw [hinter]
    exact le_normalizer_of_normal
  · change _ ≤ normalizer (((S : Subgroup H) ⊓
      (S : Subgroup H).map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H)
    rw [hinter]
    exact le_normalizer_of_normal
  · rw [hinter]
    exact hidxS
  · rw [hinter]
    exact hidxT
  · intro B hBS hBQ
    rw [hinter] at hBQ ⊢
    exact original_omega_fixedIndex_lower_of_natural_quotient hF S hu K e q hq hk E hE B hBS hBQ
  · intro B hBT hBQ
    rw [hinter] at hBQ ⊢
    exact original_omega_fixedIndex_lower_of_natural_quotient hF T huT K e q hq hk E hE B hBT hBQ

/-- Source4.5 for the literal original Sylow pair, with the actual natural
omega quotient still supplied by its independent recognition owner. -/
theorem original_exists_elementary_intersection_row
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (q : H →* SL2FourNatural.SL) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (omegaCenterIn (pCore 2 H) : Set H))
    (E : (Additive (omegaCenterIn (pCore 2 H)) ⧸ fixedSpace (omegaAction H) ⊤)
      ≃ₗ[ZMod 2] SL2FourNatural.V)
    (hE : ∀ h v, E (fixedQuotient (omegaAction H) ⊤ h v) =
      specialLinearNatural 2 (q h) (E v)) :
    ∃ g : H,
      (S : Subgroup H) ⊔ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = pCore 2 H ∧
      ∃ n, let P : IntersectionPair H :=
        ⟨S,(S : Subgroup H).map (MulAut.conj g).toMonoidHom,twistedConjugacy (S : Subgroup H) α g⟩
        IsElementaryAbelian 2 ↥((P.row n).left ⊓ (P.row n).right) := by
  obtain ⟨g,hgen,hinter,hpair⟩ := original_numerical_pair_of_natural_quotient
    hF S α hu K e hno q hq hk E hE
  refine ⟨g,hgen,hinter,?_⟩
  exact IntersectionPair.exists_elementary_row _ hpair
/-- The elementary row exists under the original Main Hypothesis alone;
the actual natural quotient and its coordinates are constructed by source2.9. -/
theorem original_psl2_four_elementary_maximum_row
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α) :
    ∃ g : H,
      (S : Subgroup H) ⊔ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = pCore 2 H ∧
      ∃ n, let P : IntersectionPair H :=
        ⟨S,(S : Subgroup H).map (MulAut.conj g).toMonoidHom,twistedConjugacy (S : Subgroup H) α g⟩
        let Q := (P.row n).left ⊓ (P.row n).right
        IsElementaryAbelian 2 Q ∧ Q ∈ thompsonAbelianSubgroups (S : Subgroup H) ∧
          Q ∈ thompsonAbelianSubgroups ((S : Subgroup H).map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨q,hq,hk,_,_,_,E,hE⟩ := original_psl2_four_omegaAction_recognition
    hF S hu K e hf hno.noCharacteristicNormal
  obtain ⟨g,hgen,hinter,hpair⟩ := original_numerical_pair_of_natural_quotient
    hF S α hu K e hno q hq hk E hE
  exact ⟨g,hgen,hinter,IntersectionPair.exists_elementary_maximum_row _ hpair⟩
end Glauberman
