module

public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# An index-four kernel from a central subgroup of order eight

A finite group of order 96 with a central subgroup of order 8 has a normal
subgroup of index 4. In a Sylow two-subgroup the central subgroup has index 4,
so the Sylow derived subgroup has order at most 2. Transfer to the Sylow
abelianization has image of order at least 4: its restriction to the central
subgroup is the odd Sylow-index power. A quotient of this two-group image
of order 4 supplies the required kernel.

This is the local transfer calculation in Suzuki (1965), Section II,
Lemma 3, in the whole-torus branch. Neither cyclicity of the central subgroup
nor recognition of the central quotient is needed for this conclusion.
-/

namespace Subgroup

private theorem derived_card_le_two_of_central_index_four
    {P : Type*} [Group P] [Finite P]
    (Z : Subgroup P) [Z.Normal] (hZ : Z ≤ center P)
    (hindex : Z.index = 4) : Nat.card (_root_.commutator P) ≤ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (P ⧸ Z) = 4 := hindex
  by_cases hc : IsCyclic (P ⧸ Z)
  · let := hc
    have hcomm : IsMulCommutative P :=
      (QuotientGroup.mk' Z).isMulCommutative_of_isCyclic_of_ker_le_center
        (by simpa only [QuotientGroup.ker_mk'] using hZ)
    rw [(commutator_eq_bot_iff P).mpr hcomm, card_bot]
    decide
  · let : IsMulCommutative (P ⧸ Z) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard
    have hpow (x : P ⧸ Z) : x ^ 2 = 1 := by
      have hd : orderOf x ∣ 2 ^ 2 := by
        simpa only [hcard, show (2 : ℕ) ^ 2 = 4 by rfl] using _root_.orderOf_dvd_natCard x
      obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      have hnlt : n < 2 := by
        by_contra h
        have hn2 : n = 2 := by omega
        exact hc (isCyclic_of_orderOf_eq_card x (by rw [he, hn2, hcard]; rfl))
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [he]
      exact (pow_dvd_pow 2 (show n ≤ 1 by omega)).trans (by simp)
    let : IsElementaryAbelian 2 (P ⧸ Z) :=
      ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow⟩
    exact card_commutator_le_two_of_central_elementary_four_quotient Z hZ hcard

/-- A two-group quotient of order at least four yields a normal index-four subgroup. -/
public theorem exists_normal_index_four_of_twoGroup_image
    {G A : Type*} [Group G] [Group A] [Finite A]
    (f : G →* A) (hf : Function.Surjective f) (hA : IsPGroup 2 A)
    (hcard : 4 ≤ Nat.card A) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hnle
    rw [← hn] at hp
    omega
  obtain ⟨L, hL, _, hLc⟩ := exists_normal_subgroup_card_pow_of_normal
    (G := A) (p := 2) (⊤ : Subgroup A) inferInstance
    (by simpa only [card_top] using hn) (n - 2) (by omega)
  let : L.Normal := hL
  have hLi : L.index = 4 := by
    have hm := L.card_mul_index
    rw [hLc, hn] at hm
    have he : 2 ^ n = 2 ^ (n - 2) * 4 := by
      calc
        2 ^ n = 2 ^ ((n - 2) + 2) := by congr 1; omega
        _ = 2 ^ (n - 2) * 4 := by rw [pow_add]; rfl
    rw [he] at hm
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hm
  exact ⟨L.comap f, inferInstance, (L.index_comap_of_surjective hf).trans hLi⟩

/-- Every group of order 96 with a central subgroup of order 8 has a normal
subgroup of index 4. -/
public theorem exists_normal_index_four_of_card_ninetySix_of_central_eight
    {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E = 96) (Z : Subgroup E)
    (hZ : Nat.card Z = 8) (hcentral : Z ≤ center E) :
    ∃ N : Subgroup E, N.Normal ∧ N.index = 4 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Z.Normal := ⟨fun z hz g => by
    rw [mem_center_iff.mp (hcentral hz) g, mul_inv_cancel_right]
    exact hz⟩
  let P : Sylow 2 E := Sylow.nonempty.some
  have hPcard : Nat.card P = 32 := by
    rw [P.card_eq_multiplicity, hE]
    decide +kernel
  have hPi : (P : Subgroup E).index = 3 := by
    have hm := (P : Subgroup E).card_mul_index
    rw [hPcard, hE] at hm
    omega
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n := 3) hZ
  have hZP : Z ≤ (P : Subgroup E) := hZtwo.le_sylow_of_normal P
  let ZP := Z.subgroupOf (P : Subgroup E)
  have hZPc : Nat.card ZP = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv).trans hZ
  have hZPcenter : ZP ≤ center P := by
    intro z hz
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext (mem_center_iff.mp (hcentral hz) (p : E))
  have hZPi : ZP.index = 4 := by
    have hm := ZP.card_mul_index
    rw [hZPc, hPcard] at hm
    omega
  have hD := derived_card_le_two_of_central_index_four ZP hZPcenter hZPi
  let f : P →* Abelianization P := Abelianization.of
  let : Finite (Abelianization P) :=
    Finite.of_surjective (Abelianization.of : P →* Abelianization P) Quotient.mk_surjective
  let tr : E →* Abelianization P := MonoidHom.transfer f
  let r : Z →* Abelianization P := tr.comp Z.subtype
  have hrker : Nat.card r.ker ≤ 2 := by
    let i : r.ker → _root_.commutator P := fun z => by
      let zP : P := ⟨((z : Z) : E), hZP z.val.property⟩
      have hkey : ∀ (k : ℕ) (g : E),
          g⁻¹ * (zP : E) ^ k * g ∈ (P : Subgroup E) →
            g⁻¹ * (zP : E) ^ k * g = (zP : E) ^ k := by
        intro k g _
        have hc := mem_center_iff.mp ((center E).pow_mem (hcentral z.val.property) k) g
        calc
          _ = g⁻¹ * (g * (zP : E) ^ k) := by rw [mul_assoc, hc.symm]
          _ = _ := inv_mul_cancel_left _ _
      have hztr : tr (zP : E) = 1 := z.property
      have hpow : f zP ^ 3 = 1 := by
        have he := MonoidHom.transfer_eq_pow f (zP : E) hkey
        change tr (zP : E) = f (zP ^ (P : Subgroup E).index) at he
        rw [he, map_pow, hPi] at hztr
        exact hztr
      have hdiv : orderOf (f zP) ∣ 32 :=
        hPcard ▸ (orderOf_map_dvd f zP).trans (_root_.orderOf_dvd_natCard zP)
      have hone : f zP = 1 := orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 32 3)
          hdiv (orderOf_dvd_of_pow_eq_one hpow))
      have hzD : zP ∈ _root_.commutator P := by
        change zP ∈ Abelianization.of.ker at hone
        rwa [Abelianization.ker_of] at hone
      exact ⟨zP, hzD⟩
    have hi : Function.Injective i := by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      simpa only [i] using congrArg (fun z : _root_.commutator P => ((z : P) : E)) he
    exact (Nat.card_le_card_of_injective i hi).trans hD
  have hrange : 4 ≤ Nat.card tr.range := by
    have hm := r.ker.card_mul_index
    rw [index_ker, hZ] at hm
    have hpos : 0 < Nat.card r.ker := Nat.card_pos
    have hrl : 4 ≤ Nat.card r.range := by nlinarith
    exact hrl.trans (card_le_of_le (by
      rintro _ ⟨z, rfl⟩
      exact ⟨(z : E), rfl⟩ : r.range ≤ tr.range))
  have hAtwo : IsPGroup 2 (Abelianization P) :=
    P.isPGroup'.of_surjective Abelianization.of Quotient.mk_surjective
  exact exists_normal_index_four_of_twoGroup_image tr.rangeRestrict
    tr.rangeRestrict_surjective (hAtwo.to_subgroup tr.range) hrange

end Subgroup
