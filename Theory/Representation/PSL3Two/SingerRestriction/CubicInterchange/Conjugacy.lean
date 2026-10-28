module

public import Theory.Representation.PSL3Two.SingerRestriction.FiveSpace

/-!
# Simultaneous conjugacy of Singer–cubic pairs

First conjugate the order-seven subgroup to the symmetric Singer group.
Then apply Sylow conjugacy inside its normalizer to align the cubic subgroup.
The absence of a factor nine in 168 makes every order-three subgroup of that
normalizer Sylow. This preserves the literal pair and requires no exhaustive
search through pairs of subgroups.

Source: Aschbacher–Smith J.2.3(7), printed p.434 (PDF p.445),
combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Matrix Representation Representation.BinaryOffender
namespace BinaryLinearThree.SingerRestriction.CubicInterchange
open Matrix.PSL3Two.OuterInvolutionSinger FiveSpace.Certificate

lemma conjugate_cubic_in (N K D : Subgroup Group) (hKN : K ≤ N) (hDN : D ≤ N)
    (hK : Nat.card K = 3) (hD : Nat.card D = 3) :
    ∃ n : N, K.map (MulAut.conj (n : Group)).toMonoidHom = D := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcard (A : Subgroup Group) (hAN : A ≤ N) (hA : Nat.card A = 3) :
      Nat.card (A.subgroupOf N) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv).trans hA
  let syl (A : Subgroup Group) (hAN : A ≤ N) (hA : Nat.card A = 3) : Sylow 3 N :=
    (IsPGroup.of_card (n := 1) (by simpa using hcard A hAN hA)).toSylow (by
      intro hi
      have hd : 9 ∣ Nat.card N := by
        rw [← (A.subgroupOf N).card_mul_index, hcard A hAN hA]
        exact Nat.mul_dvd_mul_left 3 hi
      have he := hd.trans N.card_subgroup_dvd_card
      rw [Matrix.PSL3Two.card_SL] at he
      norm_num at he)
  obtain ⟨n,hn⟩ := MulAction.exists_smul_eq N (syl K hKN hK) (syl D hDN hD)
  have he : (K.subgroupOf N).map (MulAut.conj n).toMonoidHom = D.subgroupOf N :=
    congrArg (fun P : Sylow 3 N => (P : Subgroup N)) hn
  refine ⟨n, ?_⟩
  calc
    K.map (MulAut.conj (n : Group)).toMonoidHom =
        ((K.subgroupOf N).map N.subtype).map (MulAut.conj (n : Group)).toMonoidHom := by
      rw [map_subgroupOf_eq_of_le hKN]
    _ = ((K.subgroupOf N).map (MulAut.conj n).toMonoidHom).map N.subtype := by
      rw [Subgroup.map_map,Subgroup.map_map]
      rfl
    _ = D := by rw [he,map_subgroupOf_eq_of_le hDN]

lemma cubic_normalizes_singer : zpowers cubic ≤ normalizer (zpowers singer) := by
  apply zpowers_le.mpr
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  have hc : (MulAut.conj cubic) singer = singer ^ 2 := by decide
  change zpowers ((MulAut.conj cubic) singer) = zpowers singer
  rw [hc]
  apply le_antisymm
  · exact zpowers_le.mpr ((zpowers singer).pow_mem (mem_zpowers singer) 2)
  · apply zpowers_le.mpr
    have he : singer = (singer ^ 2) ^ 4 := by
      rw [← pow_mul]
      change singer = singer ^ (7+1)
      rw [pow_succ, show singer ^ 7 = 1 by decide, one_mul]
    exact (congrArg (fun x => x ∈ zpowers (singer ^ 2)) he).mpr
      ((zpowers (singer ^ 2)).pow_mem (mem_zpowers _) 4)
lemma cubic_card : Nat.card (zpowers cubic) = 3 := by
  rw [Nat.card_zpowers]
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide : cubic ^ 3 = 1) (by decide : cubic ≠ 1)

lemma pair_conjugacy (H D : Subgroup Group) (hH : Nat.card H = 7)
    (hD : Nat.card D = 3) (hDH : D ≤ normalizer H) :
    ∃ t : Group, (zpowers singer).map (MulAut.conj t).toMonoidHom = H ∧
      (zpowers cubic).map (MulAut.conj t).toMonoidHom = D := by
  obtain ⟨a,ha⟩ := exists_conjugate_singer H hH
  let K := (zpowers cubic).map (MulAut.conj a).toMonoidHom
  have hK : Nat.card K = 3 :=
    (Nat.card_congr ((MulAut.conj a).subgroupMap (zpowers cubic)).toEquiv).symm.trans cubic_card
  have hKN : K ≤ normalizer H := by
    rw [← ha, ← map_equiv_normalizer_eq]
    exact map_mono cubic_normalizes_singer
  obtain ⟨n,hn⟩ := conjugate_cubic_in (normalizer H) K D hKN hDH hK hD
  have hcomp : (MulAut.conj ((n : Group)*a)).toMonoidHom =
      (MulAut.conj (n : Group)).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  refine ⟨(n : Group)*a, ?_, ?_⟩
  · rw [hcomp, ← Subgroup.map_map,ha]
    exact mem_normalizer_iff_map_conj_eq.mp n.property
  · rw [hcomp, ← Subgroup.map_map]
    exact hn
end BinaryLinearThree.SingerRestriction.CubicInterchange
