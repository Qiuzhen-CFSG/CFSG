module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups.Intersection
public import Glauberman.DicksonClassification
import Mathlib.GroupTheory.Complement

/-!
# Dickson reduction for prime-field Sylow overgroups

A proper subgroup of PSL₂ over an odd prime field that contains a Sylow
two-subgroup is dihedral, A₄, S₄, or A₅. The Sylow subgroup is noncyclic,
excluding cyclic groups and Borel subgroups: its map to the cyclic Borel
quotient is injective because the kernel has odd order. Elementary groups
are excluded by parity. A prime field has no proper subfield alternatives;
the full-degree PSL₂ alternative has the ambient order and hence is not
proper.

Apply this calculation to the literal inner intersection of the original
PGL₂ overgroup. The extension from that intersection to the whole overgroup
is a separate obligation. Source: Huppert II.8.27 (Dickson), used in the
prime-field calculation for Aschbacher--Smith E.1.14(6), printed p.214.
-/

noncomputable section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups

open Subgroup GorensteinWalter
open scoped Pointwise

variable {F : Type*} [Field F] [Finite F]

omit [Field F] [Finite F] in
/-- Odd prime fields satisfy the odd-prime-power convention used by the
projective group APIs, with exponent exactly one. -/
public theorem oddPrimePower_of_prime_card {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p) : IsOddPrimePower (Nat.card F) :=
  ⟨p, 1, Fact.out, hpodd, le_rfl, by simpa using hFcard⟩

/-- Dickson's remaining alternatives for a proper prime-field PSL₂ Sylow
overgroup. The isomorphisms concern the given subgroup itself. -/
public theorem prime_psl_sylow_overgroup_cases {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p)
    (S : Sylow 2 (PSL2 F)) (H : Subgroup (PSL2 F))
    (hSH : (S : Subgroup _) ≤ H) (hH : H ≠ ⊤) :
    (∃ z : ℕ,
      (z ∣ (Nat.card F - 1) / 2 ∨ z ∣ (Nat.card F + 1) / 2) ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
    Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
    Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  classical
  have hF := oddPrimePower_of_prime_card hpodd hFcard
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
    obtain ⟨a, ha⟩ := hpodd
    exact ⟨a, by omega⟩
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := p) (f := 1) (by simpa using hFcard) H with
    hElementary | hCyclic | hDihedral | hA4 | hS4 | hA5 | hBorel | hPSL | hPGL
  · exfalso
    have hHp : IsPGroup p H := IsElementaryAbelian.isPGroup p H
    exact hSnotP ((hHp.to_subgroup SH).of_equiv
      (Subgroup.subgroupOfEquivOfLe hSH))
  · exfalso
    let : IsCyclic H := hCyclic.choose_spec.2.2
    exact hSnotcyclic (Subgroup.isCyclic_of_le hSH)
  · exact Or.inl (by simpa only [hgcd] using hDihedral)
  · exact Or.inr (Or.inl hA4.2)
  · exact Or.inr (Or.inr (Or.inl hS4.2))
  · exact Or.inr (Or.inr (Or.inr hA5.2))
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
    obtain ⟨m, _hm, hmdiv, ⟨eH⟩⟩ := hPSL
    have hm : m = 1 := Nat.dvd_one.mp hmdiv
    subst m
    let K := GaloisField p 1
    have hKcard : Nat.card K = Nat.card F := by
      simpa only [K, pow_one, hFcard] using GaloisField.card p 1 (by decide)
    have hK : IsOddPrimePower (Nat.card K) := hKcard ▸ hF
    apply hH (Subgroup.eq_top_of_card_eq (H := H) ?_)
    calc
      Nat.card H = Nat.card (PSL2 K) := Nat.card_congr eH.toEquiv
      _ = Nat.card (PSL2 F) := by
        rw [psl2_card_formula K hK, psl2_card_formula F hF, hKcard]
  · exfalso
    obtain ⟨m, hm, hmdiv, _eH⟩ := hPGL
    have heq : 2 * m = 1 := Nat.dvd_one.mp hmdiv
    omega

/-- Apply the preceding exhaustion to the literal inner intersection of the
PGL₂ overgroup. This discharges the elementary, cyclic, Borel, and subfield
branches without assuming an extension classification. -/
public theorem inner_dickson_cases {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hTM : (T : Subgroup _) ≤ M) (hM : M ≠ ⊤) :
    (∃ z : ℕ,
      (z ∣ (Nat.card F - 1) / 2 ∨ z ∣ (Nat.card F + 1) / 2) ∧
      Nat.card (inner M) = 2 * z ∧ Nonempty (inner M ≃* DihedralGroup z)) ∨
    Nonempty (inner M ≃* alternatingGroup (Fin 4)) ∨
    Nonempty (inner M ≃* Equiv.Perm (Fin 4)) ∨
    Nonempty (inner M ≃* alternatingGroup (Fin 5)) := by
  have hF := oddPrimePower_of_prime_card hpodd hFcard
  obtain ⟨S, hS⟩ := exists_sylow_le_inner hF T M hTM
  exact prime_psl_sylow_overgroup_cases hpodd hFcard S (inner M) hS
    (inner_ne_top hF T M hTM hM)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups
