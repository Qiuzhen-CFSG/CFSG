module

public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Central subgroups and subgroups of coprime index

In a finite perfect group, a central subgroup Z contained in H lies in
H′ whenever |Z| is coprime to |G:H|. Transfer to H/H′ kills G′ and
acts on Z by the index power; coprimality makes that power injective.

This is the transfer step for restriction of a cubic central cover to
a hexad stabilizer of index 77 in Aschbacher--Smith 13.8.21(2), p.956.
The conclusion concerns H′; survival in H∞ requires further hypotheses.
-/

namespace Subgroup

public theorem central_le_mapped_commutator_of_coprime_index {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (H Z : Subgroup G) (hZ : Z ≤ center G) (hZH : Z ≤ H)
    (hc : (Nat.card Z).Coprime H.index) :
    Z ≤ (_root_.commutator H).map H.subtype := by
  intro x hx
  let xH : H := ⟨x, hZH hx⟩
  let f : H →* Abelianization H := Abelianization.of
  let t : G →* Abelianization H := MonoidHom.transfer f
  have ht : t x = 1 := Abelianization.commutator_subset_ker t
    (Group.IsPerfect.mem_commutator (g := x))
  have hkey : ∀ (k : ℕ) (g : G),
      g⁻¹ * x ^ k * g ∈ H → g⁻¹ * x ^ k * g = x ^ k := by
    intro k g _
    have he := mem_center_iff.mp ((center G).pow_mem (hZ hx) k) g
    rw [mul_assoc, he.symm, inv_mul_cancel_left]
  have hpow : f xH ^ H.index = 1 := by
    have he : t x = f (xH ^ H.index) := MonoidHom.transfer_eq_pow f x hkey
    rw [he, map_pow] at ht
    exact ht
  have hd : orderOf (f xH) ∣ Nat.card Z := by
    have hz := _root_.orderOf_dvd_natCard (⟨x, hx⟩ : Z)
    rw [← Subgroup.orderOf_coe] at hz
    exact (orderOf_map_dvd f xH).trans ((Subgroup.orderOf_coe xH) ▸ hz)
  have ho : orderOf (f xH) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hc.coprime_dvd_left hd) dvd_rfl
      (orderOf_dvd_of_pow_eq_one hpow)
  have hf : f xH = 1 := orderOf_eq_one_iff.mp ho
  have hm : xH ∈ _root_.commutator H := by
    change xH ∈ Abelianization.of.ker at hf
    rwa [Abelianization.ker_of] at hf
  exact ⟨xH, hm, rfl⟩


end Subgroup
