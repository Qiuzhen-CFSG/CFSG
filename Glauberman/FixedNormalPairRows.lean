module
public import Glauberman.FixedNormalPairRecursion

/-!
# Maximum abelian order at the elementary row

The sharp replacement theorem identifies the maximum abelian families of
each intersection with families of both preceding members. Consequently the
elementary intersection obtained by finite descent has the full maximum
abelian order of both original members. This is the initial maximum-order
part of Niles4.6(b), before translating across the full intersection array.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma4.3(c) and
Proposition4.6(b), printedpp44,46.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

/-- Maximum abelian families of the current intersection remain maximum
in both members of the numerical pair. -/
theorem NumericalPair.maximum_families {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPair S T φ) :
    thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups S ∧
    thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups T := by
  have hS : S ≠ ⊥ := by
    intro he
    have hh := h.index_left
    rw [he,relIndex_bot_right] at hh
    omega
  have hh := fixed_normal_pair_counting S T (omegaCenterIn (S ⊓ T)) φ hS h.no_fixed
    h.normal_left h.normal_right
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) inferInstance
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
    (fun B hB hBQ => by rw [h.index_left]; exact h.lower_left B hB.1 hBQ)
    (fun B hB hBQ => by rw [h.index_right]; exact h.lower_right B hB.1 hBQ)
  exact ⟨hh.2.2.2.2.1,hh.2.2.2.2.2.1⟩

namespace IntersectionPair
/-- The terminal elementary intersection has the full maximum abelian order
of both original members. This retains the source4.6(b) conclusion along
the finite descent, rather than merely finding an arbitrary elementary subgroup. -/
theorem exists_elementary_maximum_row (P : IntersectionPair G)
    (h : NumericalPair P.left P.right P.equiv) :
    ∃ n, let Q := (P.row n).left ⊓ (P.row n).right
      IsElementaryAbelian 2 Q ∧ Q ∈ thompsonAbelianSubgroups P.left ∧
        Q ∈ thompsonAbelianSubgroups P.right := by
  generalize he : Nat.card P.left = m
  induction m using Nat.strong_induction_on generalizing P with
  | h m ih =>
    obtain ⟨hfamilyS,hfamilyT⟩ := h.maximum_families
    rcases h.recursion with hE | ⟨hnext,_⟩
    · let _ := hE
      have hmax : P.left ⊓ P.right ∈ thompsonAbelianSubgroups (P.left ⊓ P.right) :=
        ⟨le_rfl,inferInstance,fun _ hle _ => card_le_of_le hle⟩
      exact ⟨0,hE,hfamilyS hmax,hfamilyT hmax⟩
    · obtain ⟨n,hEn,hmaxS,hmaxT⟩ := ih (Nat.card P.next.left)
        (he ▸ P.next_card_lt h) P.next hnext rfl
      exact ⟨n + 1,hEn,hfamilyS hmaxT,hfamilyT hmaxT⟩
end IntersectionPair
end Glauberman
