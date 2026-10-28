module

public import Theory.GroupTheory.PGroup.NormalizerBarrier
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Uniqueness of abelian subgroups across p-overgroups

An abelian subgroup which is the unique subgroup of its order and type in
its normalizer remains unique inside every p-overgroup containing it.
Conjugating it inside the normalizer of an intermediate p-subgroup preserves
its order and abelianness. The p-group normalizer condition therefore puts
the entire p-overgroup in the original normalizer.

Sylow conjugacy transports uniqueness from one Sylow subgroup when the
candidate is normal. For a cubic extension of an abelian group of order 27,
a fixed subgroup of order three gives the needed local uniqueness: a second
abelian group of order 27 would intersect the first in at least nine elements,
all fixed by the actor of order three.

These are the local-to-Sylow steps in Bender, *Finite groups with large
subgroups* (1974), proof of (4.1), printed p.225.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Local uniqueness forces every p-overgroup to normalize the candidate. -/
public theorem p_overgroup_le_normalizer_of_unique_abelian
    {p : ℕ} [Fact p.Prime] (A : Subgroup G) [IsMulCommutative A]
    (hunique : ∀ B : Subgroup G, B ≤ normalizer (A : Set G) →
      IsMulCommutative B → Nat.card B = Nat.card A → B = A)
    (P : Subgroup G) (hP : IsPGroup p P) (hAP : A ≤ P) :
    P ≤ normalizer (A : Set G) := by
  apply p_overgroup_le_of_normalizers_le hP hAP A.le_normalizer
  intro W _ hAW hWN g hg
  rw [mem_normalizer_iff_map_conj_eq]
  apply hunique (A.map (MulAut.conj g).toMonoidHom) _ inferInstance
    (card_map_of_injective (MulAut.conj g).injective)
  have hm := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hAW
  have he : W.map (MulAut.conj g).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp hg
  exact (hm.trans he.le).trans hWN

/-- Local uniqueness persists in every p-overgroup containing the candidate. -/
public theorem eq_of_same_card_abelian_in_p_overgroup
    {p : ℕ} [Fact p.Prime] (A : Subgroup G) [IsMulCommutative A]
    (hunique : ∀ B : Subgroup G, B ≤ normalizer (A : Set G) →
      IsMulCommutative B → Nat.card B = Nat.card A → B = A)
    (P : Subgroup G) (hP : IsPGroup p P) (hAP : A ≤ P)
    (B : Subgroup G) (hBP : B ≤ P) (hB : IsMulCommutative B)
    (hcard : Nat.card B = Nat.card A) : B = A := by
  exact hunique B (hBP.trans
    (p_overgroup_le_normalizer_of_unique_abelian A hunique P hP hAP)) hB hcard

/-- For a normal candidate, uniqueness in one Sylow subgroup suffices. -/
public theorem eq_of_abelian_card_of_unique_in_sylow
    {p : ℕ} [Fact p.Prime] (A : Subgroup G) [A.Normal]
    (P : Sylow p G)
    (hunique : ∀ B : Subgroup G, B ≤ (P : Subgroup G) →
      IsMulCommutative B → Nat.card B = Nat.card A → B = A)
    (B : Subgroup G) (hBp : IsPGroup p B) (hB : IsMulCommutative B)
    (hcard : Nat.card B = Nat.card A) : B = A := by
  let : IsMulCommutative B := hB
  obtain ⟨Q, hBQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have he := congrArg Sylow.toSubgroup hg
  change (Q : Subgroup G).map (MulAut.conj g).toMonoidHom = (P : Subgroup G) at he
  have hBmap := hunique (B.map (MulAut.conj g).toMonoidHom)
    ((map_mono hBQ).trans he.le) inferInstance
    ((card_map_of_injective (MulAut.conj g).injective).trans hcard)
  apply (map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)
  exact hBmap.trans (Normal.map_conj_eq (H := A) g).symm

/-- The fixed-subgroup order excludes a second abelian subgroup of order 27. -/
public theorem eq_of_abelian_order27_in_cubic_extension
    (A X : Subgroup G) [IsMulCommutative A]
    (hA : Nat.card A = 27) (hX : Nat.card X = 3)
    (hXA : X ≤ normalizer (A : Set G)) (hd : Disjoint A X)
    (hfixed : Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 3)
    (B : Subgroup G) (hB : B ≤ A ⊔ X) (hBc : IsMulCommutative B)
    (hcard : Nat.card B = 27) : B = A := by
  let : IsMulCommutative B := hBc
  have hPcard : Nat.card (A ⊔ X : Subgroup G) = 81 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A X hXA hd, hA, hX]
  by_contra hne
  have hBn : B ≤ normalizer (A : Set G) :=
    hB.trans (sup_le A.le_normalizer hXA)
  let T := A ⊔ B
  have hTP : T ≤ A ⊔ X := sup_le le_sup_left hB
  have hAT : A ≤ T := le_sup_left
  have hcA : Nat.card (A.subgroupOf T) = 27 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv).trans hA
  have hi := (A.subgroupOf T).index_mul_card
  rw [hcA] at hi
  have hdiv : Nat.card T ∣ 81 := hPcard ▸ card_dvd_of_le hTP
  have hidiv : (A.subgroupOf T).index ∣ 3 := by
    have hm : (A.subgroupOf T).index * 27 ∣ 3 * 27 := by
      simpa only [hi] using hdiv
    exact Nat.dvd_of_mul_dvd_mul_right (by decide) hm
  have hTc : Nat.card T = 81 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hidiv with hone | hthree
    · have hTA : T ≤ A := subgroupOf_eq_top.mp (index_eq_one.mp hone)
      exact (hne (eq_of_le_of_card_ge (le_sup_right.trans hTA)
        (by rw [hA, hcard]))).elim
    · omega
  have hT : T = A ⊔ X := eq_of_le_of_card_ge hTP (by rw [hTc, hPcard])
  have hcomm : T ≤ centralizer (A ⊓ B : Set G) := sup_le
    (A.le_centralizer.trans (centralizer_le inf_le_left))
    (B.le_centralizer.trans (centralizer_le inf_le_right))
  have hXcomm : X ≤ centralizer (A ⊓ B : Set G) :=
    (show X ≤ A ⊔ X from le_sup_right).trans (hT.symm.le.trans hcomm)
  have hinf : A ⊓ B ≤ A ⊓ centralizer (X : Set G) :=
    le_inf inf_le_left (le_centralizer_iff.mpr hXcomm)
  have hsmall := card_le_of_le hinf
  rw [hfixed] at hsmall
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hBn
  rw [hA, hcard, show Nat.card (A ⊔ B : Subgroup G) = 81 from hTc] at hprod
  omega
end Subgroup
