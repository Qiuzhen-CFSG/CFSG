module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import Theory.Alternating.proposition_5_2_7_8
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Centers and marked actions in the exceptional alternating cases

The exceptional multiplier bounds the center by six. Once its order is odd,
the center is trivial or is actually isomorphic to the cyclic group of order
three. In the trivial case the literal quotient map is an isomorphism; in
both cases a specified quotient action gives the canonical alternating-action
conclusion without any further recognition premise.

The oddness premise is explicit: excluding the even covers is a separate
source obligation. Perfectness and simplicity exclude alternating degrees
below five by embedding their permutation groups in the solvable S₄.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed pp.502--503;
GLS, Volume 3, Theorem 5.2.3.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
open Chapter15.Section03.Candidates.ComponentStructure

variable {L : Type*} [Group L]

/-- The original central quotient map becomes an equivalence when its kernel
is trivial. Its definition preserves the quotient marking. -/
noncomputable def quotientEquivOfCenterBot (hz : center L = ⊥) : L ≃* L ⧸ center L :=
  MulEquiv.ofBijective (QuotientGroup.mk' (center L))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hz]),
      QuotientGroup.mk'_surjective _⟩

variable [IsQuasisimple L]

/-- No degree below five can occur as the central quotient of a quasisimple group. -/
theorem five_le_degree {n : ℕ} (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    5 ≤ n := by
  by_contra hn
  have hn4 : n ≤ 4 := by omega
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let f : (L ⧸ center L) →* Equiv.Perm (Fin 4) :=
    (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn4)).comp
      ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom)
  have hf : Function.Injective f :=
    (Equiv.Perm.viaEmbeddingHom_injective _).comp
      (Subtype.val_injective.comp e.injective)
  exact Group.IsPerfect.not_isSolvable (L ⧸ center L)
    (Group.isSolvable_of_isSolvable_injective hf)

variable [Finite L]

/-- The exceptional multiplier and an odd center give exactly the simple or
cyclic-three center alternatives, in any universe. -/
theorem center_bot_or_equiv_three {n : ℕ}
    (e : L ⧸ center L ≃* alternatingGroup (Fin n)) (hn : n = 6 ∨ n = 7)
    (hodd : Odd (Nat.card (center L))) :
    center L = ⊥ ∨ Nonempty (center L ≃* Multiplicative (ZMod 3)) := by
  have hd := GLS3.Chapter5.exceptional_alternating_center_card_dvd_six n e hn
  have hd3 : Nat.card (center L) ∣ 3 := hodd.coprime_two_right.dvd_of_dvd_mul_left
    (by simpa using hd)
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd3 with hc | hc
  · exact Or.inl (Subgroup.card_eq_one.mp hc)
  · exact Or.inr ⟨mulEquivOfPrimeCardEq hc (by simp)⟩

/-- A marked permutation action descends to the exact simple/triple output.
Only the exclusion of even centers remains explicit. -/
theorem action_of_odd_center {α : MulAut L} {n : ℕ}
    (e : L ⧸ center L ≃* alternatingGroup (Fin n)) (hn : n = 6 ∨ n = 7)
    (hodd : Odd (Nat.card (center L))) (σ : Equiv.Perm (Fin n))
    (ha : ∀ x : L,
      (e (QuotientGroup.mk' (center L) (α x)) : Equiv.Perm (Fin n)) =
        σ * e (QuotientGroup.mk' (center L) x) * σ⁻¹) :
    AlternatingAction α n σ := by
  rcases center_bot_or_equiv_three e hn hodd with hz | hz
  · exact Or.inl ⟨(quotientEquivOfCenterBot hz).trans e, ha⟩
  · exact Or.inr ⟨inferInstance, hz, e, ha⟩

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
