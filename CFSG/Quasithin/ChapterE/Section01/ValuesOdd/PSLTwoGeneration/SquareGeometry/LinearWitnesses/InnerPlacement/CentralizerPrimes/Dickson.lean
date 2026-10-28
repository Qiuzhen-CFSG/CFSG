module

public import GorensteinWalter.PSL2DihedralSylow
public import Glauberman.DicksonClassification
import Mathlib.GroupTheory.Complement
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

/-!
# Dickson alternatives for prime-square Sylow overgroups

A proper subgroup of PSL₂(p²) containing a full Sylow two-subgroup is
dihedral, S₄, or a genuine PGL₂(p) subfield group. The Sylow order is
divisible by eight, excluding A₄ and A₅. Noncyclicity and coprime kernel
arguments exclude cyclic and elementary-by-cyclic alternatives. The
PSL₂(p) alternative has even ambient index, while PSL₂(p²) has full order.

The PGL₂ alternative retains Dickson's actual `SubfieldConjugacyWitness`;
no unconnected family label or prime-field maximal-subgroup list is used.
The elementary and Borel eliminations adapt the existing prime-field
`PrimeGeometry.Diagonal.MaximalOvergroups.DicksonReduction` proof.
Source: Huppert II.8.27, used for Aschbacher--Smith E.1.14(6), printed p.214.
-/

public section

open Subgroup GorensteinWalter
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes

private theorem square_order_factor {p : ℕ} (hp : Odd p) :
    p ^ 2 * ((p ^ 2) ^ 2 - 1) / 2 =
      (p * (p ^ 2 + 1)) * (p * (p ^ 2 - 1) / 2) := by
  have h2 : 2 ∣ p ^ 2 - 1 := (by decide : 2 ∣ 8).trans (Nat.eight_dvd_sq_sub_one_of_odd hp)
  have hf : (p ^ 2) ^ 2 - 1 = (p ^ 2 + 1) * (p ^ 2 - 1) := by
    simpa using Nat.pow_two_sub_pow_two (p ^ 2) 1
  rw [hf, ← mul_assoc, Nat.mul_div_assoc _ h2, Nat.mul_div_assoc _ h2]
  ring

/-- The full ambient Sylow has order divisible by eight, including p = 5. -/
theorem square_sylow_eight_dvd {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (S : Sylow 2 (PSL2 F)) : 8 ∣ Nat.card S := by
  apply S.pow_dvd_card_of_pow_dvd_card (n := 3)
  have hF : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, hpodd, by decide, hFcard⟩
  rw [psl2_card_formula F hF, hFcard]
  obtain ⟨a, ha⟩ := Nat.eight_dvd_sq_sub_one_of_odd hpodd
  have he : p ^ 2 = 8 * a + 1 := by
    have hp1 := (Fact.out : p.Prime).one_lt
    have hp2 : 1 ≤ p ^ 2 := by nlinarith
    omega
  have hf : (p ^ 2) ^ 2 - 1 = 16 * (a * (4 * a + 1)) := by
    rw [he]
    have hh : (8 * a + 1) ^ 2 = 16 * (a * (4 * a + 1)) + 1 := by ring
    omega
  rw [hf]
  have hh : p ^ 2 * (16 * (a * (4 * a + 1))) =
      2 * (8 * (p ^ 2 * (a * (4 * a + 1)))) := by ring
  rw [hh, Nat.mul_div_right _ (by decide : 0 < 2)]
  exact dvd_mul_right _ _

/-- Genuine Dickson alternatives for proper overgroups of a full Sylow in
prime-square PSL₂. The projective subfield embedding is retained. -/
theorem square_sylow_overgroup_cases {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (S : Sylow 2 (PSL2 F)) (H : Subgroup (PSL2 F))
    (hSH : (S : Subgroup _) ≤ H) (hH : H ≠ ⊤) :
    (∃ z : ℕ,
      (z ∣ (Nat.card F - 1) / 2 ∨ z ∣ (Nat.card F + 1) / 2) ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
    (Nonempty (H ≃* PGL2 (GaloisField p 1)) ∧
      Nonempty (Glauberman.Dickson.SubfieldConjugacyWitness p 1 H)) := by
  have h8H : 8 ∣ Nat.card H :=
    (square_sylow_eight_dvd hpodd hFcard S).trans (card_dvd_of_le hSH)
  classical
  have hF : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, hpodd, by decide, hFcard⟩
  obtain ⟨k, hk, ⟨eS⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF S
  have hSnotcyclic : ¬ IsCyclic S := by
    intro h
    exact DihedralGroup.not_isCyclic
      (ne_of_gt (Nat.one_lt_pow (by omega : k ≠ 0) (by norm_num : 1 < 2)))
      (eS.isCyclic.mp h)
  have hScard : Nat.card S = 2 * 2 ^ k :=
    (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
  have hSnotP : ¬ IsPGroup p S := by
    intro hSp
    obtain ⟨a, ha⟩ := hSp.exists_card_eq
    have hodd : Odd (Nat.card S) := ha ▸ hpodd.pow
    exact hodd.not_two_dvd_nat (hScard ▸ dvd_mul_right 2 (2 ^ k))
  let SH : Subgroup H := (S : Subgroup (PSL2 F)).subgroupOf H
  have hSH2 : IsPGroup 2 SH :=
    S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
    apply Nat.dvd_gcd ?_ (dvd_refl 2)
    rw [hFcard]
    exact (by decide : 2 ∣ 8).trans (Nat.eight_dvd_sq_sub_one_of_odd hpodd)
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield
      (p := p) (f := 2) hFcard H with
    hElementary | hCyclic | hDihedral | hA4 | hS4 | hA5 | hBorel | hPSL | hPGL
  · exfalso
    have hHp : IsPGroup p H := IsElementaryAbelian.isPGroup p H
    exact hSnotP ((hHp.to_subgroup SH).of_equiv
      (Subgroup.subgroupOfEquivOfLe hSH))
  · exfalso
    let : IsCyclic H := hCyclic.choose_spec.2.2
    exact hSnotcyclic (Subgroup.isCyclic_of_le hSH)
  · exact Or.inl (by simpa only [hgcd] using hDihedral)
  · exfalso
    have hc : Nat.card H = 12 := by
      rw [Nat.card_congr hA4.2.some.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hd := h8H
    rw [hc] at hd
    norm_num at hd
  · exact Or.inr (Or.inl hS4.2)
  · exfalso
    have hc : Nat.card H = 60 := by
      rw [Nat.card_congr hA5.2.some.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hd := h8H
    rw [hc] at hd
    norm_num at hd
  · exfalso
    obtain ⟨m, t, _ht, _htF, N, C, hNnormal, hNelem, _hNcard,
      hCcyclic, _hCcard, hdisjoint, hsup⟩ := hBorel
    let : N.Normal := hNnormal
    have hcomp : N.IsComplement' C := by
      refine ⟨Subgroup.mul_injective_of_disjoint hdisjoint, ?_⟩
      intro g
      have hg : g ∈ (N : Set H) * (C : Set H) := by
        rw [← Subgroup.normal_mul N C, hsup]
        trivial
      obtain ⟨n, hn, c, hc, hnc⟩ := hg
      exact ⟨⟨⟨n, hn⟩, ⟨c, hc⟩⟩, hnc⟩
    let eQ : H ⧸ N ≃* C := hcomp.symm.QuotientMulEquiv
    let : IsCyclic (H ⧸ N) := eQ.isCyclic.mpr hCcyclic
    have hNp : IsPGroup p N := IsElementaryAbelian.isPGroup p N
    have h2p : 2 ≠ p := by
      intro h
      exact hpodd.not_two_dvd_nat (h ▸ dvd_refl 2)
    have hcoprime : Nat.Coprime (Nat.card SH) (Nat.card N) :=
      IsPGroup.coprime_card_of_ne 2 p h2p SH N hSH2 hNp
    have hinf : SH ⊓ N = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcoprime).eq_bot
    let q : SH →* H ⧸ N := (QuotientGroup.mk' N).comp SH.subtype
    have hqker : q.ker = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxN : (x : H) ∈ N :=
        (QuotientGroup.eq_one_iff (N := N) (x : H)).mp hx
      have hxinf : (x : H) ∈ SH ⊓ N := ⟨x.property, hxN⟩
      rw [hinf] at hxinf
      exact Subtype.ext (Subgroup.mem_bot.mp hxinf)
    have hcyclic : IsCyclic SH := isCyclic_of_injective q ((MonoidHom.ker_eq_bot_iff q).mp hqker)
    exact hSnotcyclic ((Subgroup.subgroupOfEquivOfLe hSH).isCyclic.mp hcyclic)
  · exfalso
    obtain ⟨m, hm, hmdiv, ⟨eH⟩, _hw⟩ := hPSL
    rcases (Nat.dvd_prime Nat.prime_two).mp hmdiv with rfl | rfl
    · have hKcard : Nat.card (GaloisField p 1) = p := by
        simpa using GaloisField.card p 1 (by decide)
      have hK : IsOddPrimePower (Nat.card (GaloisField p 1)) :=
        ⟨p, 1, Fact.out, hpodd, by decide, by simpa⟩
      have hc : Nat.card (PSL2 F) = (p * (p ^ 2 + 1)) * Nat.card H := by
        rw [Nat.card_congr eH.toEquiv, psl2_card_formula F hF,
          psl2_card_formula (GaloisField p 1) hK, hFcard, hKcard]
        exact square_order_factor hpodd
      have hi : H.index = p * (p ^ 2 + 1) := by
        apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card H from Nat.card_pos)
        exact H.index_mul_card.trans hc
      have h2 : 2 ∣ H.index := by
        rw [hi]
        apply dvd_mul_of_dvd_right
        exact (hpodd.pow.add_odd (by decide : Odd (1 : ℕ))).two_dvd
      exact S.not_dvd_index (h2.trans (index_dvd_of_le hSH))
    · let K := GaloisField p 2
      have hKcard : Nat.card K = Nat.card F := by
        simpa only [K, hFcard] using GaloisField.card p 2 (by decide)
      have hK : IsOddPrimePower (Nat.card K) := hKcard ▸ hF
      apply hH (Subgroup.eq_top_of_card_eq (H := H) ?_)
      calc
        Nat.card H = Nat.card (PSL2 K) := Nat.card_congr eH.toEquiv
        _ = Nat.card (PSL2 F) := by
          rw [psl2_card_formula K hK, psl2_card_formula F hF, hKcard]
  · obtain ⟨m, hm, hmdiv, eH, hw⟩ := hPGL
    have hm1 : m = 1 := by
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hmdiv
      omega
    subst m
    exact Or.inr (Or.inr ⟨eH, hw⟩)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes
