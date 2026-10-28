module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.Inputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.LocalFacts
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions
public import Theory.GroupTheory.CComponent.ThreeResidual

/-!
# The actual component and three-residual in the S₆ branch

The component image is a nontrivial perfect normal subgroup of S₆, hence
exactly A₆. This identifies K/Z(K), without identifying a central cover
with its quotient. The vanishing odd core gives Z(K) = O₂(K). The rank-two
centralizer argument and |Out(A₆)| = 4 make the relative normalizer index
prime to three. The full earlier conjugacy alternative bounds the remaining
normalizer index by two. Subnormal residual lifting then proves O^{3′}(Gᵥ) = K.

This proves the cited residual deduction directly, without taking A.3.18
as a parameter. Only the preceding universal `EarlierConjugates` remains
explicit, as in the construction of `ActionData`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.6.6, printed p.927; the centerless argument in A.3.18, pp.51–52.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
open A5Module
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

private theorem componentImage_normal {H : Type*} [Group H] (K : Subgroup H) :
    (NormalizerAction.componentImage K).Normal := by
  exact (inferInstance : (K.subgroupOf (normalizer (K : Set H))).Normal).map
    (NormalizerAction.quotient K) (QuotientGroup.mk'_surjective _)

omit [Finite G] in
/-- The image of K in the prescribed S₆ quotient is its alternating subgroup. -/
theorem component_image_eq_alternating
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e : XStar K ≃* Equiv.Perm (Fin 6)) :
    (NormalizerAction.componentImage K).map e.toMonoidHom = alternatingGroup (Fin 6) := by
  let : IsQuasisimple K := hK.2
  let I := NormalizerAction.componentImage K
  let J := I.map e.toMonoidHom
  let eI := I.equivMapOfInjective e.toMonoidHom e.injective
  let ec := (NormalizerAction.componentCentralQuotientEquiv K).trans eI
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial J := ec.symm.surjective.nontrivial
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := ec.toMonoidHom) ec.surjective
  let : I.Normal := componentImage_normal K
  let : J.Normal := (inferInstance : I.Normal).map e.toMonoidHom e.surjective
  change J = alternatingGroup (Fin 6)
  apply le_antisymm
  · rw [← commutator_eq_self (H := J)]
    exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
  · exact Equiv.Perm.alternatingGroup_le_of_normal (by simp) inferInstance

/-- The central quotient of the actual embedded component is A₆. -/
noncomputable def componentCentralQuotientEquivSix
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e : XStar K ≃* Equiv.Perm (Fin 6)) :
    (K ⧸ center K) ≃* alternatingGroup (Fin 6) :=
  (NormalizerAction.componentCentralQuotientEquiv K).trans
    (((NormalizerAction.componentImage K).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (component_image_eq_alternating K hK e)))

/-- The odd-core hypothesis identifies the central quotient with K/O₂(K). -/
noncomputable def componentTwoCoreQuotientEquivSix
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e : XStar K ≃* Equiv.Perm (Fin 6)) :
    (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6) := by
  let : IsQuasisimple K := hK.2
  have hc := IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hodd K)
  exact (QuotientGroup.quotientMulEquivOfEq hc.symm).trans
    (componentCentralQuotientEquivSix K hK e)

private theorem component_primeToResidual_eq_top
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e : XStar K ≃* Equiv.Perm (Fin 6)) : primeToResidual 3 K = ⊤ := by
  let : IsQuasisimple K := hK.2
  let eK := componentTwoCoreQuotientEquivSix hodd K hK e
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := eK.isSimpleGroup
  have hp : IsPPerfect 2 K := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (K ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  apply primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 K) pCore_isPGroup hp
  rw [Nat.card_congr eK.toEquiv, alternatingGroup.SixSubgroupObstructions.card_six]
  decide

private theorem component_relative_index_coprime_three
    (d : Setup κ T s)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e : XStar K ≃* Equiv.Perm (Fin 6)) : Nat.Coprime 3 (K.relIndex (X K)) := by
  let D := K.subgroupOf (X K)
  let eD : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe K.le_normalizer)
      (pCore_map_iso 2 _)).trans (componentTwoCoreQuotientEquivSix hodd K hK e)
  have hz : center (D ⧸ pCore 2 D) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he := (centerCongr eD ⟨z, hz⟩).property
    change eD z ∈ center (alternatingGroup (Fin 6)) at he
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact eD.map_eq_one_iff.mp he
  have hrD : 2 ≤ primeRank 3 (D ⧸ pCore 2 D) := by
    rw [primeRank_congr 3 eD]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (D ⧸ pCore 2 D))) := by
    rw [Nat.card_congr (MulAut.outerCongr eD).toEquiv,
      AlternatingSix.ShadowLocal.outer_card]
    decide
  have hr : primeRank 3 (Gv (markedV s)) ≤ 2 :=
    (d.ambient.involution_centralizer_sqtk (marked_orders s).2).stronglyQuasithin
      3 Nat.prime_three (by decide)
  exact cComponent_index_coprime_three_of_quotient D
    (hK.isCComponent.subgroupOf K.le_normalizer) hz hrD
    ((_root_.primeRank_le_of_injective 3 (X K).subtype (X K).subtype_injective).trans hr) ho

/-- The source equality O^{3′}(Gᵥ) = K, including the possible central cover. -/
theorem primeToResidual_eq_component
    (d : Setup κ T s) (earlier : EarlierConjugates κ)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e : XStar K ≃* Equiv.Perm (Fin 6)) :
    primeToResidual 3 (Gv (markedV s)) = K := by
  have hn := Chapter1.Section02.proposition_1_2_1_three_index_of_A_3_8 earlier
    (Chapter1.Section02.uniqueness_local_quotient_sqtk d.ambient d.local115.mem_H)
    hK.isCComponent
  have hcop : Nat.Coprime 3 (X K).index := by
    rcases hn with hn | ⟨hi, _⟩
    · let := hn
      simp only [X, normalizer_eq_top, index_top]
      decide
    · rw [hi]
      decide
  apply primeToResidual_eq_of_subnormal_coprime_index 3 K hK.1
    (component_primeToResidual_eq_top hodd K hK e)
  rw [← relIndex_mul_index K.le_normalizer]
  exact (component_relative_index_coprime_three d hodd K hK e).mul_right hcop

/-- The actual marked Lᵥ is contained in K. -/
theorem residual_le_component
    (d : Setup κ T s) (m : ModuleData s) (earlier : EarlierConjugates κ)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e : XStar K ≃* Equiv.Perm (Fin 6)) : residual s ≤ K := by
  rw [← primeToResidual_eq_component d earlier hodd K hK e]
  exact residual_le_primeToResidual s m.residual_quotient_card
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
