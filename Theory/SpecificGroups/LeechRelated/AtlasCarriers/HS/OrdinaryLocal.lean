module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ElementarySylowFixers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Overgroups
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.LocalGeneration
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreOrder
public import Theory.GroupAction.InnerSylowFixers
public import Theory.GroupTheory.DoubleCoverCentralizer.SylowCenterConjugacy

/-!
# Sylow centralizers in the Higman--Sims carrier

The certified pointwise Sylow fixer bound, together with the trivial center,
forces the Sylow center to have order two and every Sylow fixer to be inner.
The central involution normalizer maps onto S₅. Its order is therefore divisible
by five, whereas the other certified Sylow overgroup has order 10752. The
Sylow overgroup classification makes the involution centralizer maximal;
conjugacy of Sylow centers transports this conclusion to every two-central
involution.

These are the intrinsic model inputs for the ordinary component case, including
central two-covers, in Aschbacher--Smith 15.1.20(3d), printed pp.1096--1097.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
namespace Sporadic.LeechRelated.HS.OrdinaryLocal
open EvenLocalCandidates BlockNormalizer
open EvenLocalCandidates.CentralInvolutionCore

private theorem sylow_nontrivial (P : Sylow 2 Carrier) : Nontrivial P := by
  apply (Finite.one_lt_card_iff_nontrivial).mp
  rw [Nat.card_congr (P.equiv baseSylow).toEquiv]
  change 1 < Nat.card subgroup
  rw [subgroup_card]
  decide

/-- Every automorphism fixing a Sylow two-subgroup pointwise is inner. -/
theorem automorphism_inner_of_fixes_sylow (P : Sylow 2 Carrier) (a : MulAut Carrier)
    (ha : ∀ x ∈ P, a x = x) : ∃ t : Carrier, a = MulAut.conj t := by
  let := sylow_nontrivial P
  obtain ⟨z,hz⟩ := Theory.GroupAction.sylow_fixer_inner_of_card_le_two
    center_carrier_eq_bot P (ElementarySylowFixers.sylow_fixer_card_le_two P) a ha
  exact ⟨z.val,hz⟩

/-- Every Sylow two-subgroup has a center of order two. -/
theorem sylow_center_card_two (P : Sylow 2 Carrier) : Nat.card (center P) = 2 := by
  let := sylow_nontrivial P
  let : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  apply Nat.le_antisymm _ Finite.one_lt_card
  let f : center P →* MulAut Carrier := MulAut.conj.comp
    ((P : Subgroup Carrier).subtype.comp (center P).subtype)
  have hf : Function.Injective f :=
    (MulAut.conj_injective_of_center_eq_bot center_carrier_eq_bot).comp
      ((P : Subgroup Carrier).subtype_injective.comp (center P).subtype_injective)
  rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  apply ElementarySylowFixers.sylow_fixer_card_le_two P
  rintro a ⟨z,rfl⟩ x hx
  change (z.val : Carrier) * x * (z.val : Carrier)⁻¹ = x
  apply mul_inv_eq_iff_eq_mul.mpr
  exact (congrArg Subtype.val (mem_center_iff.mp z.property (⟨x,hx⟩ : P))).symm

private theorem e0_order : orderOf e0 = 2 :=
  orderOf_eq_prime_iff.mpr ⟨by simpa [pow_two] using e0_mul, e0_nontrivial⟩

private theorem first_eq_centralizer : localGroup 0 = centralizer ({e0} : Set Carrier) := by
  have he : elementary 0 = zpowers e0 := by
    rw [zpowers_eq_closure]
    unfold elementary
    congr 1
    ext x
    constructor
    · rintro ⟨j,hj,rfl⟩
      have hj0 : j = 0 := Fin.ext (by simpa using hj)
      subst j
      rfl
    · rintro rfl
      exact ⟨0,by simp,rfl⟩
  rw [localGroup,he]
  exact normalizer_zpowers_eq_centralizer_of_order_two e0 e0_order

private theorem marked_centralizer_isCoatom : IsCoatom (localGroup 0) := by
  have hproper : localGroup 0 ≠ ⊤ := by
    rw [first_eq_centralizer]
    intro he
    have hc : e0 ∈ center Carrier := by
      apply mem_center_iff.mpr
      intro x
      exact mem_centralizer_singleton_iff.mp (he.symm ▸ mem_top x)
    rw [center_carrier_eq_bot,mem_bot] at hc
    exact e0_nontrivial hc
  have hfive : 5 ∣ Nat.card (localGroup 0) := by
    have hd := Subgroup.card_dvd_of_surjective
      CentralNormalizerThreePart.PairQuotient.fiveHom
      CentralNormalizerThreePart.PairQuotient.fiveHom_surjective
    have hc : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
      decide
    rw [hc] at hd
    exact (by decide : 5 ∣ 120).trans hd
  have hsecond : Nat.card baseNormalizer = 10752 := by
    obtain ⟨f⟩ := baseNormalizer_quotient_of_surjective baseNormalizer_action_surjective
    have hi : (pCore 2 baseNormalizer).index = 168 :=
      (Nat.card_congr f.toEquiv).trans Matrix.PSL3Two.card_SL
    rw [← (pCore 2 baseNormalizer).card_mul_index,model_core_card,hi]
  refine ⟨hproper, ?_⟩
  intro U hU
  by_contra hne
  rcases SylowOvergroups.proper_overgroup_le U
    ((LocalGeneration.sylow_le_member 0).trans hU.le) hne with h | h
  · exact hU.ne (le_antisymm hU.le h)
  · have hd := hfive.trans (card_dvd_of_le (hU.le.trans h))
    change 5 ∣ Nat.card baseNormalizer at hd
    rw [hsecond] at hd
    norm_num at hd

/-- The centralizer of each two-central involution is maximal. -/
theorem twoCentral_centralizer_isCoatom (t : Carrier) (ht : orderOf t = 2)
    (hc : TwoCentral t) : IsCoatom (centralizer ({t} : Set Carrier)) := by
  have hzP : e0 ∈ baseSylow :=
    elementary_le_subgroup 0 (subset_closure ⟨0,by simp,rfl⟩)
  have hz : TwoCentral e0 := by
    refine ⟨baseSylow,hzP,mem_center_iff.mpr ?_⟩
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (first_eq_centralizer ▸ LocalGeneration.sylow_le_member 0 x.property)
  apply hc.centralizer_isCoatom_of_center_card_two hz
    (fun he => by rw [he,orderOf_one] at ht; omega)
    e0_nontrivial sylow_center_card_two
  rw [← first_eq_centralizer]
  exact marked_centralizer_isCoatom

end Sporadic.LeechRelated.HS.OrdinaryLocal
