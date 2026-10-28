module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.Alternating.proposition_5_2_6

/-!
# S₄ fixed subgroups of natural outer involutions of A₆

For a transposition, an arbitrary permutation of the other four letters has
one even extension, obtained by correcting its sign on the transposed pair.
This embeds S₄ in the actual fixed subgroup, whose order is 24. Conjugation
transports this model to every transposition. The exceptional automorphism
of S₆ sends our transposition to three disjoint transpositions, and its
restriction to A₆ transports the fixed subgroup as well. Finally, the cycle
length and sign formulas show that every odd involution of S₆ has one of
these two cycle types.

The finite checks concern only the explicit six-letter permutations and the
order of the standard fixed subgroup; they are checked by Lean's kernel.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.567–570, especially the fixed-subgroup
containment argument in Lemma 2.5.26 on p.569.
-/

public section

open Equiv Equiv.Perm Subgroup GLS3.Chapter5

namespace AlternatingSix.ShadowLocal

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private def signPair : ℤˣ →* Perm (Fin 2) where
  toFun s := if s = 1 then 1 else swap 0 1
  map_one' := by simp
  map_mul' a b := by
    rcases Int.units_eq_one_or a with rfl | rfl <;>
      rcases Int.units_eq_one_or b with rfl | rfl <;> decide

private def fourLetterExtension : Perm (Fin 4) →* Perm (Fin 6) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6)).toMonoidHom.comp
    ((sumCongrHom (Fin 4) (Fin 2)).comp
      ((MonoidHom.id (Perm (Fin 4))).prod (signPair.comp sign)))

private theorem fourLetterExtension_even (σ : Perm (Fin 4)) :
    fourLetterExtension σ ∈ alternatingGroup (Fin 6) := by
  rw [mem_alternatingGroup]
  change sign ((finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6).permCongr
    (Equiv.sumCongr σ (signPair (sign σ)))) = 1
  rw [sign_permCongr, sign_sumCongr]
  rcases Int.units_eq_one_or (sign σ) with h | h <;> rw [h] <;> decide

private theorem fourLetterExtension_fixed : ∀ σ,
    swap (4 : Fin 6) 5 * fourLetterExtension σ * (swap 4 5)⁻¹ =
      fourLetterExtension σ := by
  decide +kernel

/-- Extend a permutation of the first four letters to an even permutation,
using its sign to decide whether to swap the last two letters. -/
def standardSwapEmbedding : Perm (Fin 4) →* A6 :=
  fourLetterExtension.codRestrict _ fourLetterExtension_even

/-- The embedding retains the given action on the four complementary letters. -/
theorem standardSwapEmbedding_apply (σ : Perm (Fin 4)) (i : Fin 4) :
    (standardSwapEmbedding σ).val (Fin.castAdd 2 i) = Fin.castAdd 2 (σ i) := by
  change (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6)
    (Equiv.sumCongr σ (signPair (sign σ)) (finSumFinEquiv.symm (Fin.castAdd 2 i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem standardSwapEmbedding_injective : Function.Injective standardSwapEmbedding := by
  intro σ τ h
  have hp := (Equiv.permCongrHom finSumFinEquiv).injective (congrArg Subtype.val h)
  have hq := sumCongrHom_injective hp
  exact congrArg Prod.fst hq

/-- Fixedness is conjugation on the actual six-point alternating group. -/
theorem standardSwapEmbedding_fixed (σ : Perm (Fin 4)) :
    permutationAction (swap 4 5) (standardSwapEmbedding σ) = standardSwapEmbedding σ :=
  Subtype.ext (fourLetterExtension_fixed σ)

private def standardSwapFixedHom : Perm (Fin 4) →*
    automorphismFixedSubgroup (permutationAction (swap 4 5)) :=
  standardSwapEmbedding.codRestrict _ standardSwapEmbedding_fixed

private theorem standardSwapFixed_card :
    Nat.card (automorphismFixedSubgroup (permutationAction (swap 4 5))) = 24 := by
  change Nat.card {g : A6 // permutationAction (swap 4 5) g = g} = 24
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The fixed subgroup of the standard transposition is S₄, via the even
extension of its action on the other four letters. -/
noncomputable def standardSwapFixedEquiv :
    automorphismFixedSubgroup (permutationAction (swap 4 5)) ≃* Perm (Fin 4) :=
  (MulEquiv.ofBijective standardSwapFixedHom
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨
      fun _ _ h => standardSwapEmbedding_injective (congrArg Subtype.val h), by
        rw [standardSwapFixed_card]
        norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]⟩)).symm

/-- The inverse is the specified even extension, rather than an abstract
isomorphism inferred from the order of the fixed subgroup. -/
theorem standardSwapFixedEquiv_symm_coe (σ : Perm (Fin 4)) :
    (standardSwapFixedEquiv.symm σ).val = standardSwapEmbedding σ := by rfl

private theorem natural_action_intertwines (σ τ p : Perm (Fin 6))
    (hp : p * σ * p⁻¹ = τ) (g : A6) :
    permutationAction p (permutationAction σ g) =
      permutationAction τ (permutationAction p g) := by
  have he : permutationAction p * permutationAction σ =
      permutationAction τ * permutationAction p := by
    rw [← map_mul, ← map_mul]
    exact congrArg permutationAction (mul_inv_eq_iff_eq_mul.mp hp)
  exact congrArg (fun a : AutA6 => a g) he

/-- Transport fixed subgroups by the same six-point conjugation as the
permutations defining their automorphisms. -/
noncomputable def naturalFixedConjugacyEquiv (σ τ p : Perm (Fin 6))
    (hp : p * σ * p⁻¹ = τ) :
    automorphismFixedSubgroup (permutationAction σ) ≃*
      automorphismFixedSubgroup (permutationAction τ) :=
  fixedSubgroupMulEquivOfCompat (permutationAction p) _ _
    (natural_action_intertwines σ τ p hp)

theorem naturalFixedConjugacyEquiv_apply (σ τ p : Perm (Fin 6))
    (hp : p * σ * p⁻¹ = τ) (g : automorphismFixedSubgroup (permutationAction σ)) :
    (naturalFixedConjugacyEquiv σ τ p hp g).val = permutationAction p g.val :=
  fixedSubgroupMulEquivOfCompat_apply _ _ _ _ _

/-- Every transposition acting by conjugation on A₆ fixes a copy of S₄. -/
noncomputable def swapFixedEquiv (σ : Perm (Fin 6)) (hσ : σ.IsSwap) :
    automorphismFixedSubgroup (permutationAction σ) ≃* Perm (Fin 4) := by
  have hc : IsConj σ (swap (4 : Fin 6) 5) :=
    isConj_of_cycleType_eq ((isSwap_iff_cycleType.mp hσ).trans
      (show (swap (4 : Fin 6) 5).cycleType = {2} by decide +kernel).symm)
  let p := (isConj_iff.mp hc).choose
  exact (naturalFixedConjugacyEquiv σ (swap 4 5) p
    (isConj_iff.mp hc).choose_spec).trans standardSwapFixedEquiv

private theorem outer_action_intertwines (σ : Perm (Fin 6)) (g : A6) :
    outerAltAut (permutationAction σ g) =
      permutationAction (outerHom σ) (outerAltAut g) := by
  apply Subtype.ext
  change outerHom (σ * g.val * σ⁻¹) = outerHom σ * outerHom g.val * (outerHom σ)⁻¹
  simp only [map_mul, map_inv]

/-- The exceptional automorphism of S₆ restricts to A₆ and transports the
fixed subgroups of its conjugation actions. -/
noncomputable def naturalFixedOuterEquiv (σ : Perm (Fin 6)) :
    automorphismFixedSubgroup (permutationAction σ) ≃*
      automorphismFixedSubgroup (permutationAction (outerHom σ)) :=
  fixedSubgroupMulEquivOfCompat outerAltAut _ _ (outer_action_intertwines σ)

theorem naturalFixedOuterEquiv_apply (σ : Perm (Fin 6))
    (g : automorphismFixedSubgroup (permutationAction σ)) :
    (naturalFixedOuterEquiv σ g).val = outerAltAut g.val :=
  fixedSubgroupMulEquivOfCompat_apply _ _ _ _ _

theorem outerHom_standardSwap_cycleType :
    (outerHom (swap (4 : Fin 6) 5)).cycleType = {2, 2, 2} := by
  decide +kernel

/-- The three-transposition case follows from the exceptional S₆ automorphism
and conjugation on the same six-letter carrier. -/
noncomputable def tripleSwapFixedEquiv (σ : Perm (Fin 6))
    (hσ : σ.cycleType = {2, 2, 2}) :
    automorphismFixedSubgroup (permutationAction σ) ≃* Perm (Fin 4) := by
  have hc : IsConj σ (outerHom (swap (4 : Fin 6) 5)) :=
    isConj_of_cycleType_eq (hσ.trans outerHom_standardSwap_cycleType.symm)
  let p := (isConj_iff.mp hc).choose
  exact ((naturalFixedConjugacyEquiv σ (outerHom (swap 4 5)) p
    (isConj_iff.mp hc).choose_spec).trans
      (naturalFixedOuterEquiv (swap 4 5)).symm).trans standardSwapFixedEquiv

/-- Cycle lengths divide two, the support has at most six letters, and odd
sign excludes the double-transposition case. -/
theorem odd_involution_cycleType (σ : Perm (Fin 6)) (ho : orderOf σ = 2)
    (hn : σ ∉ alternatingGroup (Fin 6)) : σ.IsSwap ∨ σ.cycleType = {2, 2, 2} := by
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := σ.sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hsign : sign σ ≠ 1 := fun h => hn (mem_alternatingGroup.mpr h)
  rw [sign_of_cycleType', hk] at hsign
  have hkbound : k ≤ 2 := by omega
  interval_cases k
  · exact Or.inl (isSwap_iff_cycleType.mpr (by simpa using hk))
  · norm_num at hsign
  · exact Or.inr (by simpa using hk)

/-- Every natural outer involution of Aut(A₆) has fixed subgroup S₄. All
permutation and cycle-type premises are discharged from the stated inputs. -/
theorem natural_outer_involution_fixed_equiv_symmetricFour
    (β : AutA6) (hβ : orderOf β = 2) (hn : β ∈ natural) (hi : β ∉ inner) :
    Nonempty (automorphismFixedSubgroup β ≃* Perm (Fin 4)) := by
  obtain ⟨σ, hσ⟩ := hn
  change permutationAction σ = β at hσ
  subst β
  have ho : orderOf σ = 2 :=
    (orderOf_injective permutationAction permutationAction_injective σ).symm.trans hβ
  have hodd : σ ∉ alternatingGroup (Fin 6) := by
    intro heven
    exact hi ⟨⟨σ, heven⟩, (permutationAction_coe ⟨σ, heven⟩).symm⟩
  rcases odd_involution_cycleType σ ho hodd with hs | ht
  · exact ⟨swapFixedEquiv σ hs⟩
  · exact ⟨tripleSwapFixedEquiv σ ht⟩

end AlternatingSix.ShadowLocal
