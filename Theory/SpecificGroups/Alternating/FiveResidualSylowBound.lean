module
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# A Sylow bound from the actual A5 residual quotient

If O²(G)/O₂(O²(G)) is A5, then G/O₂(G) acts faithfully on that normal
A5 image: its centralizer lies in the residual and the latter has trivial
center. The embedding in Aut(A5) = S5 bounds its Sylow two-group by eight.
Restoring the literal two-core gives |T| ≤ 8 |O₂(G)|.

Source: the classical automorphism theorem for A5, as proved in
Theory.Alternating.Aut; application in Aschbacher–Smith 5.1.13, p.638.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.FiveResidualSylowBound
variable {G : Type*} [Group G] [Finite G]
/-- The original Sylow is bounded by the two-core and the A5 automizer. -/
theorem sylow_card_le_eight_mul_core
    (P : Sylow 2 G)
    (e : ((pResidual 2 G) ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5)) :
    Nat.card P ≤ 8 * Nat.card (pCore 2 G) := by
  let Q := pCore 2 G
  let q := QuotientGroup.mk' Q
  have hq := QuotientGroup.mk'_surjective Q
  let R := pResidual 2 (G ⧸ Q)
  have hR : (pResidual 2 G).map q = R := map_pResidual_of_surjective 2 q hq
  let eR : R ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr hR.symm).trans
      ((coreQuotientEquivImage 2 (pResidual 2 G)).symm.trans e)
  have hc : centralizer (R : Set (G ⧸ Q)) = ⊥ := by
    apply bot_unique
    intro x hx
    have hr : x ∈ R := centralizer_pResidual_le_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) hx
    have hz : (⟨x,hr⟩ : R) ∈ center R := by
      apply mem_center_iff.mpr
      intro r
      exact Subtype.ext (hx r r.property)
    have hh := MulEquivClass.apply_mem_center eR hz
    change eR ⟨x,hr⟩ ∈ center (alternatingGroup (Fin 5)) at hh
    rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 5)),mem_bot] at hh
    exact congrArg Subtype.val (eR.injective (hh.trans eR.map_one.symm))
  let f : (G ⧸ Q) →* Equiv.Perm (Fin 5) :=
    Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.symm.toMonoidHom.comp
      ((MulAut.congr eR).toMonoidHom.comp (MulAut.conjNormal : (G ⧸ Q) →* MulAut R))
  have hf : Function.Injective f :=
    Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.symm.injective.comp
      ((MulAut.congr eR).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot R hc))
  let S := P.mapSurjective hq
  obtain ⟨J,hJ⟩ := (S.isPGroup'.map f).exists_le_sylow
  have hJc : Nat.card J = 8 := by
    rw [Sylow.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    norm_num [Nat.factorial]
    rw [show (120 : ℕ).factorization 2 = 3 by
      rw [show 120 = 2^3*15 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 15)]]
    norm_num
  have hSc : Nat.card S ≤ 8 := by
    rw [←card_map_of_injective hf (K := (S : Subgroup (G ⧸ Q)))]
    exact (card_le_of_le hJ).trans_eq hJc
  have he := card_eq_card_quotient_mul_card_subgroup (q.subgroupMap (P : Subgroup G)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (q.subgroupMap (P : Subgroup G)) (q.subgroupMap_surjective _)).toEquiv,
    ker_subgroupMap,QuotientGroup.ker_mk',
    Nat.card_congr (subgroupOfEquivOfLe (pCore_isPGroup.le_sylow_of_normal P)).toEquiv] at he
  exact he.trans_le (Nat.mul_le_mul_right _ hSc)

end Theory.SpecificGroups.Alternating.FiveResidualSylowBound
