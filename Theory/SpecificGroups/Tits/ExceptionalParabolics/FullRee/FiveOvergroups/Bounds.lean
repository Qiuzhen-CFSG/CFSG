module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Embedding
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max8

/-!
# Large Sylow-five overgroups in the full binary Ree group

The derived Tits subgroup has index two, and is itself a counterexample to an
unqualified assertion that every proper large Sylow-five overgroup has order
15600. For a subgroup which does not contain the derived group, the native
Tits five-overgroup coverage bounds its intersection with the derived group
by 7800. Equality identifies that intersection with the literal fourth ATLAS
candidate, after conjugacy. The relative index is at most two.

This supplies the numerical finite-group input to Aschbacher–Smith J.5.4.
The source intersection argument separately excludes the derived alternative;
no exhaustive full-Ree classification or PSL₂(25) identification is assumed.
-/

@[expose] public section
open Subgroup
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.FiveOvergroups
abbrev R := ReeF4.Model 0
abbrev D := commutator R
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
def derivedPart (J : Subgroup R) : Subgroup Atlas1600Group :=
  (J.subgroupOf D).map atlasDerivedEquiv.symm.toMonoidHom

theorem derivedPart_card (J : Subgroup R) :
    Nat.card (derivedPart J) = Nat.card (J ⊓ D : Subgroup R) := by
  rw [derivedPart,card_map_of_injective atlasDerivedEquiv.symm.injective]
  rw [← subgroupOf_map_subtype J D,card_map_of_injective D.subtype_injective]

theorem derivedPart_top_iff (J : Subgroup R) : derivedPart J = ⊤ ↔ D ≤ J := by
  rw [← subgroupOf_eq_top]
  constructor
  · intro h
    apply map_injective (f := atlasDerivedEquiv.symm.toMonoidHom) atlasDerivedEquiv.symm.injective
    exact h.trans (map_top_of_surjective _ atlasDerivedEquiv.symm.surjective).symm
  · intro h
    rw [derivedPart,h,map_top_of_surjective _ atlasDerivedEquiv.symm.surjective]

theorem relative_index (J : Subgroup R) : D.relIndex J = 1 ∨ D.relIndex J = 2 := by
  exact (Nat.dvd_prime Nat.prime_two).mp (derived_index ▸ relIndex_dvd_index_of_normal D J)

theorem derivedPart_card_mul (J : Subgroup R) :
    Nat.card (derivedPart J) * D.relIndex J = Nat.card J := by
  have hh := (D.subgroupOf J).card_mul_index
  have he : Nat.card (D.subgroupOf J) = Nat.card (derivedPart J) := by
    rw [derivedPart_card, ← card_map_of_injective J.subtype_injective,
      subgroupOf_map_subtype,inf_comm]
  rwa [he] at hh

theorem sylow_five_card (P : Sylow 5 R) : Nat.card P = 25 := by
  rw [P.card_eq_multiplicity,group_card]
  decide +kernel

theorem sylow_five_le_derived (P : Sylow 5 R) : (P : Subgroup R) ≤ D := by
  apply relIndex_eq_one.mp
  rcases relative_index P with h | h
  · exact h
  · have hh := relIndex_dvd_card D P
    rw [h,sylow_five_card] at hh
    norm_num at hh

theorem derived_obstruction (P : Sylow 5 R) :
    D ≠ ⊤ ∧ (P : Subgroup R) ≤ D ∧ 15600 ≤ Nat.card D ∧ Nat.card D ≠ 15600 := by
  have hc : Nat.card D = 17971200 :=
    (Nat.card_congr atlasDerivedEquiv.toEquiv).symm.trans atlas1600Group_card
  refine ⟨?_,sylow_five_le_derived P,?_,?_⟩
  · intro he
    have hh : D.index = 2 := derived_index
    rw [he,index_top] at hh
    contradiction
  · omega
  · omega

theorem five_dvd_derivedPart (J : Subgroup R) (h25 : 25 ∣ Nat.card J) :
    25 ∣ Nat.card (derivedPart J) := by
  have hh := derivedPart_card_mul J
  rcases relative_index J with h | h
  · rw [h,mul_one] at hh
    rwa [hh]
  · rw [h] at hh
    exact (Nat.Coprime.dvd_mul_right (by decide : Nat.Coprime 25 2)).mp (hh ▸ h25)

theorem derivedPart_bound (J : Subgroup R) (hD : ¬ D ≤ J)
    (h25 : 25 ∣ Nat.card J) : Nat.card (derivedPart J) ≤ 7800 := by
  obtain ⟨g,hg⟩ := MinimumIndexFiveOvergroups.coverage (derivedPart J)
    (fun ht => hD ((derivedPart_top_iff J).mp ht)) (five_dvd_derivedPart J h25)
  rcases hg with h | h
  · have hh := card_le_of_le h
    rw [card_map_of_injective (MulAut.conj g).injective] at hh
    exact hh.trans MinimumIndexCandidates.max4_card_le
  · have hh := card_le_of_le h
    rw [card_map_of_injective (MulAut.conj g).injective] at hh
    exact hh.trans (MinimumIndexCandidates.max8_card_le.trans (by decide))

theorem card_le (J : Subgroup R) (hD : ¬ D ≤ J) (h25 : 25 ∣ Nat.card J) :
    Nat.card J ≤ 15600 := by
  have hh := derivedPart_card_mul J
  have hb := derivedPart_bound J hD h25
  rcases relative_index J with hi | hi <;> rw [hi] at hh <;> omega

theorem large_derivedPart_conjugate (J : Subgroup R) (hD : ¬ D ≤ J)
    (h25 : 25 ∣ Nat.card J) (hlarge : 15600 ≤ Nat.card J) :
    Nat.card J = 15600 ∧ Nat.card (derivedPart J) = 7800 ∧ D.relIndex J = 2 ∧
    ∃ g : Atlas1600Group,
      (derivedPart J).map (MulAut.conj g).toMonoidHom = MinimumIndexCandidates.max4 := by
  have hc : Nat.card J = 15600 := Nat.le_antisymm (card_le J hD h25) hlarge
  have hb := derivedPart_bound J hD h25
  have hm := derivedPart_card_mul J
  have hi : D.relIndex J = 2 := by
    rcases relative_index J with hi | hi
    · rw [hi,hc,mul_one] at hm
      omega
    · exact hi
  have hdc : Nat.card (derivedPart J) = 7800 := by rw [hi,hc] at hm; omega
  refine ⟨hc,hdc,hi,?_⟩
  obtain ⟨g,hg⟩ := MinimumIndexFiveOvergroups.coverage (derivedPart J)
    (fun ht => hD ((derivedPart_top_iff J).mp ht)) (five_dvd_derivedPart J h25)
  rcases hg with h | h
  · refine ⟨g,eq_of_le_of_card_ge h ?_⟩
    rw [card_map_of_injective (MulAut.conj g).injective,hdc]
    exact MinimumIndexCandidates.max4_card_le
  · have hh := card_le_of_le h
    rw [card_map_of_injective (MulAut.conj g).injective,hdc] at hh
    have := MinimumIndexCandidates.max8_card_le
    omega
end Tits.ExceptionalParabolics.FullRee.FiveOvergroups
