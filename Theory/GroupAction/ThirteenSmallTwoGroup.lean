module
public import Theory.GroupAction.Lemmas
public import Mathlib.Tactic

/-!
# Thirteen does not act on a two-group of order below 4096

The powers 2⁰,...,2¹¹ have distinct residues modulo thirteen. Orbit
counting for an automorphism of order thirteen therefore makes its fixed
subgroup have the same order as the whole two-group. This excludes such
an automorphism without assuming that the group is elementary abelian.

Source: the usual coprime fixed-point counting argument. The application
to the retained two-core in Aschbacher--Smith 5.1.13 (printed pp.635--638,
refs/quasithin.pdf) is in RankOneModuleGenericExceptionalCartanLocalBinarySmallInvariant.
-/

public noncomputable section
open Subgroup
namespace MulAut

/-- A two-group of order less than 2¹² has automorphism group of order
prime to thirteen. The two-group need not be abelian. -/
theorem thirteen_coprime_of_twoGroup_card_lt {V : Type*} [Group V] [Finite V]
    (hV : IsPGroup 2 V) (hc : Nat.card V < 4096) :
    Nat.Coprime 13 (Nat.card (MulAut V)) := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  apply (by decide : Nat.Prime 13).coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨n,hn⟩ := hV.exists_card_eq
  have hnlt : n < 12 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [←hn] using hc
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 13 hd
  let P := zpowers a
  have hp : IsPGroup 13 P := IsPGroup.of_card (n := 1) (by
    simpa only [P,Nat.card_zpowers,pow_one] using ha)
  let F := FixedPoints.subgroup P V
  have hm := hp.card_modEq_card_fixedPoints V
  change Nat.card V % 13 = Nat.card F % 13 at hm
  obtain ⟨k,hkn,hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card F ∣ 2^n from hn ▸ F.card_subgroup_dvd_card)
  have hkeq : k = n := by
    have hmod : ∀ i j : Fin 12, 2^i.val % 13 = 2^j.val % 13 → i = j := by decide +kernel
    have he := hmod ⟨n,hnlt⟩ ⟨k,lt_of_le_of_lt hkn hnlt⟩ (by simpa [hn,hk] using hm)
    exact (congrArg Fin.val he).symm
  have he : Nat.card F = Nat.card V := by rw [hk,hkeq,hn]
  have ht := F.eq_top_of_card_eq he
  have hone : a = 1 := by
    apply MulEquiv.ext
    intro x
    exact (show x ∈ F from ht ▸ mem_top x) ⟨a,mem_zpowers a⟩
  rw [hone,orderOf_one] at ha
  norm_num at ha

end MulAut
