module

public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Theory.GroupTheory.CyclicSubgroupNormalizer

/-!
# A cubic supplement removes three-torsion from an involution action kernel

In a quotient of a group of three-rank at most two, an involution moving a
normal three-group has cyclic three-subgroups in its centralizer. A kernel
centralized by that involution and normalizing an independent cubic
subgroup in the same centralizer therefore has order prime to three.
The independence is literal subgroup disjointness, not a statement about
an unspecified quotient image.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel
variable {L H : Type*} [Group L] [Group H] [Finite L] [Finite H]

/-- An independent cubic subgroup prevents three-torsion in the same
involution-centralized kernel, under the original source rank bound. -/
theorem coprime_kernel_of_normal_cubic_supplement
    (f : L →* H) (hf : Function.Surjective f) (hrank : primeRank 3 L ≤ 2)
    (P : Subgroup H) [P.Normal] (hP : IsPGroup 3 P)
    (t : H) (ht : orderOf t = 2) (htP : t ∉ centralizer (P : Set H))
    (K X : Subgroup H) (hX : Nat.card X = 3) (hdisj : Disjoint K X)
    (hKX : K ≤ normalizer (X : Set H))
    (hKt : K ≤ centralizer ({t} : Set H)) (hXt : X ≤ centralizer ({t} : Set H)) :
    Nat.Coprime 3 (Nat.card K) := by
  apply (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨k,hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 hd
  let B := zpowers (k : H)
  have hkH : orderOf (k : H) = 3 :=
    (orderOf_injective K.subtype K.subtype_injective k).trans hk
  have hB : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by
    simp only [B,Nat.card_zpowers,hkH,pow_one])
  have hBK : B ≤ K := zpowers_le.mpr k.property
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hX)
  let R := B ⊔ X
  have hR : IsPGroup 3 R := hB.to_sup_of_normal_right' hX3 (hBK.trans hKX)
  have hRt : R ≤ centralizer ({t} : Set H) := sup_le (hBK.trans hKt) hXt
  let : IsCyclic R := cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
    (by decide : Odd 3) f hf hrank P hP t ht htP R hR hRt
  let kR : R := ⟨k,(show B ≤ R from le_sup_left) (mem_zpowers (k : H))⟩
  have hXR : X ≤ R := le_sup_right
  have hc : Nat.card (X.subgroupOf R) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hXR).toEquiv).trans hX
  have hkX : (k : H) ∈ X := by
    apply mem_of_pow_card_eq_one_in_cyclic (X.subgroupOf R) (x := kR)
    rw [hc]
    apply Subtype.ext
    exact hkH ▸ pow_orderOf_eq_one (k : H)
  have hkone : (k : H) = 1 := mem_bot.mp (hdisj.eq_bot ▸ (show (k : H) ∈ K ⊓ X from ⟨k.property,hkX⟩))
  have he : k = 1 := Subtype.ext hkone
  simp only [he,orderOf_one] at hk
  omega

end CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel
