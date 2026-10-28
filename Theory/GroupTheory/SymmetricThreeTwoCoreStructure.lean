module

public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.Fitting.PGroup
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Symmetric-three quotients over the two-core

A finite group with quotient S₃ over O₂ is solvable. Its odd core has
order one or three. Solvability removes the component layer, so F* = O₂
exactly when the odd core is trivial. Otherwise the odd core is the
normal two-complement O², and it centralizes O₂. The Sylow two-subgroups
have index three and are self-normalizing.

These intrinsic local facts begin the exceptional-amalgam analysis in
Aschbacher–Smith, Lemma F.6.5, printed p.305. The argument uses the
order-six quotient and Fitting theory, without an amalgam enumeration.
-/

public section

open Subgroup Theory.GroupTheory
namespace SymmetricThreeTwoCore
variable {H : Type*} [Group H] [Finite H]
variable (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
include e

omit [Finite H] in
theorem core_index : (pCore 2 H).index = 6 := by
  rw [index_eq_card, Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

omit [Finite H] in
theorem card_eq : Nat.card H = 6 * Nat.card (pCore 2 H) := by
  rw [← (pCore 2 H).index_mul_card, core_index e]

theorem solvable : Group.IsSolvable H := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 H)).mpr
    ⟨inferInstance, inferInstance⟩

theorem oddCore_card : Nat.card (pPrimeCore 2 H) = 1 ∨ Nat.card (pPrimeCore 2 H) = 3 := by
  have hd := (pPrimeCore 2 H).card_subgroup_dvd_card
  rw [card_eq e] at hd
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hc : Nat.Coprime (Nat.card (pPrimeCore 2 H)) (Nat.card (pCore 2 H)) := by
    rw [hn]
    exact pPrimeCore_coprime_card.symm.pow_right n
  have hd6 := hc.dvd_mul_right.mp hd
  have hd3 : Nat.card (pPrimeCore 2 H) ∣ 3 :=
    pPrimeCore_coprime_card.symm.dvd_mul_left.mp hd6
  exact (Nat.dvd_prime Nat.prime_three).mp hd3

theorem generalizedFitting_eq_fitting : generalizedFitting H = fittingSubgroup H := by
  let : Group.IsSolvable H := solvable e
  have hE : componentLayer H = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    let := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
  rw [generalizedFitting, hE, sup_bot_eq]

theorem characteristic_two_iff : generalizedFitting H = pCore 2 H ↔ pPrimeCore 2 H = ⊥ := by
  rw [generalizedFitting_eq_fitting e]
  constructor
  · intro h
    exact pPrimeCore_eq_bot_of_fitting_isPGroup (solvable e) 2 (h ▸ pCore_isPGroup)
  · exact Fitting_eq_pcore H 2

theorem generalizedFitting_isTwoGroup_iff :
    IsPGroup 2 (generalizedFitting H) ↔ generalizedFitting H = pCore 2 H := by
  rw [generalizedFitting_eq_fitting e]
  constructor
  · intro hp
    exact le_antisymm (le_sSup ⟨inferInstance, hp⟩) (pCore_le_fitting H 2)
  · intro hf
    rw [hf]
    exact pCore_isPGroup

theorem oddCore_card_of_not_characteristic_two
    (h : generalizedFitting H ≠ pCore 2 H) : Nat.card (pPrimeCore 2 H) = 3 := by
  rcases oddCore_card e with h1 | h3
  · exact (h ((characteristic_two_iff e).mpr (Subgroup.card_eq_one.mp h1))).elim
  · exact h3

theorem residual_eq_oddCore (h : generalizedFitting H ≠ pCore 2 H) :
    pResidual 2 H = pPrimeCore 2 H := by
  apply le_antisymm _ pPrimeCore_le_pResidual
  apply sInf_le
  refine ⟨inferInstance, ?_⟩
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  apply IsPGroup.iff_card.mpr
  refine ⟨n + 1, ?_⟩
  have hc := (pPrimeCore 2 H).index_mul_card
  rw [oddCore_card_of_not_characteristic_two e h, card_eq e, hn] at hc
  change (pPrimeCore 2 H).index = 2 ^ (n + 1)
  rw [pow_succ]
  omega

theorem core_centralizes_residual (h : generalizedFitting H ≠ pCore 2 H) :
    pCore 2 H ≤ centralizer (pResidual 2 H : Set H) := by
  rw [residual_eq_oddCore e h]
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hc : Nat.Coprime (Nat.card (pCore 2 H)) (Nat.card (pPrimeCore 2 H)) := by
    rw [hn]
    exact pPrimeCore_coprime_card.pow_left n
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_disjoint (disjoint_of_coprime_natCard hc))

 theorem sylow_index_three (S : Sylow 2 H) : (S : Subgroup H).index = 3 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 H
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let R := S.mapSurjective hf
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hR : Nat.card R = 2 := by
    rw [R.card_eq_multiplicity, hc]
    change 2 ^ (Nat.factorization (2 * 3) 2) = 2
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hi := (R : Subgroup (Equiv.Perm (Fin 3))).index_mul_card
  rw [hc, hR] at hi
  have hi3 : (R : Subgroup (Equiv.Perm (Fin 3))).index = 3 := by omega
  change ((S : Subgroup H).map f).index = 3 at hi3
  rwa [Subgroup.index_map_eq _ hf (by rw [hk]; exact pCore_isPGroup.le_sylow_of_normal S)] at hi3

 theorem sylow_self_normalizing (S : Sylow 2 H) :
    normalizer (S : Set H) = (S : Subgroup H) := by
  have hi := sylow_index_three e S
  have hm := relIndex_mul_index (S : Subgroup H).le_normalizer
  rw [hi] at hm
  have hp : ((S : Subgroup H).relIndex (normalizer (S : Set H)) *
      (normalizer (S : Set H)).index).Prime := hm ▸ Nat.prime_three
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hN⟩ | ⟨_, hS⟩
  · have htop : normalizer (S : Set H) = ⊤ := index_eq_one.mp hN
    let : (S : Subgroup H).Normal := normalizer_eq_top_iff.mp htop
    have heq : (S : Subgroup H) = pCore 2 H :=
      le_antisymm (le_sSup ⟨inferInstance, S.isPGroup'⟩)
        (pCore_isPGroup.le_sylow_of_normal S)
    rw [heq, core_index e] at hi
    norm_num at hi
  · exact le_antisymm (relIndex_eq_one.mp hS) (S : Subgroup H).le_normalizer

end SymmetricThreeTwoCore
