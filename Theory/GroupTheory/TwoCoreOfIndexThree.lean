module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

/-!
# A two-core detected inside a subgroup of index three

Let Q have index two in a two-subgroup P of a finite group G, with
|G| at most three times |P|. An element of order three normalizing Q but
not P forces Q to be normal and to contain every normal two-subgroup of G.

Indeed N_G(Q) contains P and an element of order three, so its order reaches
the ambient bound. Thus P is Sylow of index three. For any normal two-subgroup
R, the normal subgroup RQ lies between Q and P. Index two leaves only Q or P;
the latter would make P normal, contrary to the chosen element.

Application: the literal Held centralizers in GLS3 Table 5.3p's local setting,
via `Held/.../CentralizerCertificates/CoreMaximality`. No classification,
ambient order equality, Sylow status or normality of Q is assumed.
-/

open Subgroup
namespace Subgroup

public theorem normal_two_maximal_of_index_two_of_order_three
    {G : Type*} [Group G] [Finite G]
    (Q P : Subgroup G) (hQP : Q ≤ P) (hP : IsPGroup 2 P)
    (hindex : (Q.subgroupOf P).index = 2)
    (hbound : Nat.card G ≤ 3 * Nat.card P)
    (t : G) (ht : orderOf t = 3)
    (htQ : t ∈ normalizer (Q : Set G))
    (htP : t ∉ normalizer (P : Set G)) :
    Q.Normal ∧ ∀ R : Subgroup G, R.Normal → IsPGroup 2 R → R ≤ Q := by
  have hPN : P ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hQP).mp (normal_of_index_eq_two hindex)
  have hcop : Nat.Coprime 3 (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have htdiv : 3 ∣ Nat.card (normalizer (Q : Set G)) := by
    have hh := _root_.orderOf_dvd_natCard (⟨t, htQ⟩ : normalizer (Q : Set G))
    simpa only [← Subgroup.orderOf_coe, ht] using hh
  have hdiv := hcop.mul_dvd_of_dvd_of_dvd htdiv (card_dvd_of_le hPN)
  have hlower := Nat.le_of_dvd Nat.card_pos hdiv
  have hNG : Nat.card (normalizer (Q : Set G)) ≤ Nat.card G :=
    Nat.card_le_card_of_injective _ (normalizer (Q : Set G)).subtype_injective
  have hcard : Nat.card G = 3 * Nat.card P := by omega
  have hnormal : Q.Normal := normalizer_eq_top_iff.mp (((normalizer (Q : Set G)).card_eq_iff_eq_top).mp
    (by omega : Nat.card (normalizer (Q : Set G)) = Nat.card G))
  refine ⟨hnormal, ?_⟩
  have hi : P.index = 3 := by
    have hc := P.index_mul_card
    rw [hcard] at hc
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hc
  intro R hR hpR
  let : R.Normal := hR
  let : Q.Normal := hnormal
  have hRP : R ≤ P := hpR.le_sylow_of_normal (hP.toSylow (by rw [hi]; decide))
  have hsup : R ⊔ Q ≤ P := sup_le hRP hQP
  have he : Q.relIndex (R ⊔ Q) * (R ⊔ Q).relIndex P = 2 := by
    exact (Q.relIndex_mul_relIndex (R ⊔ Q) P le_sup_right hsup).trans hindex
  have hd : Q.relIndex (R ⊔ Q) ∣ 2 := ⟨_, he.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact le_sup_left.trans (relIndex_eq_one.mp h)
  · have hx : (R ⊔ Q).relIndex P = 1 := by rw [h] at he; omega
    have hEq : P = R ⊔ Q := le_antisymm (relIndex_eq_one.mp hx) hsup
    have hnP : P.Normal := hEq ▸ (inferInstance : (R ⊔ Q).Normal)
    exact (htP (by rw [@normalizer_eq_top _ _ P hnP]; trivial)).elim

end Subgroup
