module

public import Glauberman.PushingUpQuadraticOffender
public import Theory.SpecificGroups.SL2.UniqueMaximalKernel
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five

/-!
# The actual PSL₂(4) offender in Niles 2.9

The original normal kernel is kept throughout. Its intersection with the
Sylow subgroup is the two-core, so the offender constructed on the central
omega layer also lies outside that original kernel. The two quotient maps
give the same order on this actor, and its image in PSL₂(4) has order at
most four. Thus this theorem supplies the literal quadratic offender and
numerical bound used before Niles's separate recognition Lemma 2.8.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 2.2 and 2.9,
printed pp.30 and 33. This does not assert that the full central omega
layer has order sixteen: central fixed attachments remain present.
-/

public section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

theorem original_psl2_four_quadratic_offender
    (hF : Nat.card F = 4) (S : Sylow 2 G)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup G) ⊤)
    (K : Subgroup G) [K.Normal]
    (e : (G ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hno : NoCharacteristicNormal (S : Subgroup G)) :
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups (S : Subgroup G) ∧
      ¬ A ≤ K ∧
      ⁅⁅omegaCenterIn (pCore 2 G), A⁆, A⁆ = ⊥ ∧
      (omegaCenterIn (pCore 2 G) ⊓ centralizer (A : Set G)).relIndex
        (omegaCenterIn (pCore 2 G)) ≤
          Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))) ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))) =
        Nat.card (A.map (QuotientGroup.mk' K)) ∧
      Nat.card (A.map (QuotientGroup.mk' K)) ≤ 4 := by
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let b := e.trans a
  let f := b.toMonoidHom.comp (QuotientGroup.mk' K)
  have hf : Function.Surjective f := b.surjective.comp (QuotientGroup.mk'_surjective K)
  let T := S.mapSurjective hf
  have hT : Nat.card T = 4 := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card T
  have hS : (S : Subgroup G) ≠ ⊥ := by
    intro he
    have hTe : (T : Subgroup (alternatingGroup (Fin 5))) = ⊥ := by
      change (S : Subgroup G).map f = ⊥
      rw [he,Subgroup.map_bot]
    have hc : Nat.card T = 1 := by
      rw [hTe,card_bot]
    omega
  have hSK := (Theory.SpecificGroups.SL2.original_kernel_reduction_of_psl2_four
    hF S hu K e).1
  obtain ⟨A,hA,hAQ,hquad,hbound⟩ := pushingUp_quadratic_offender S hS hno
  have hAK : ¬ A ≤ K := by
    intro hAK
    exact hAQ ((le_inf hA.1 hAK).trans_eq hSK)
  have hinf : pCore 2 G ⊓ A = K ⊓ A := by
    rw [←hSK]
    ext x
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨hA.1 h.2,h.1⟩,h.2⟩⟩
  have hindex : (pCore 2 G).relIndex A = K.relIndex A := by
    rw [←inf_relIndex_right (pCore 2 G) A,
      ←inf_relIndex_right K A,hinf]
  have hcard : Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))) =
      Nat.card (A.map (QuotientGroup.mk' K)) := by
    rw [←relIndex_ker,←relIndex_ker,QuotientGroup.ker_mk',
      QuotientGroup.ker_mk',hindex]
  have hmapcard : Nat.card (A.map (QuotientGroup.mk' K)) = Nat.card (A.map f) := by
    rw [show A.map f = (A.map (QuotientGroup.mk' K)).map b.toMonoidHom from
      by rw [map_map],
      card_map_of_injective (f := b.toMonoidHom) b.injective]
  have hsmall : Nat.card (A.map (QuotientGroup.mk' K)) ≤ 4 := by
    rw [hmapcard,←hT]
    exact card_le_of_le (map_mono hA.1)
  refine ⟨A,hA,hAK,hquad,?_,hcard,hsmall⟩
  simpa only [←relIndex_ker,QuotientGroup.ker_mk'] using hbound

end Glauberman
