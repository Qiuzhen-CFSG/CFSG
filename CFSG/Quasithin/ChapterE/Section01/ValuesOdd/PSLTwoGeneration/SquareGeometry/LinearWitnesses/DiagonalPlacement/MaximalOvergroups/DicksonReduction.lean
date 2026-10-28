module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.Structure
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OvergroupModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups.Intersection
public import Glauberman.DicksonClassification
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.GroupTheory.Complement

/-!
# Dickson reduction in odd square degree

For a proper PSL₂(F) subgroup containing a Sylow two-subgroup, with |F| = p²,
Dickson's alternatives reduce to split dihedral groups with rotation order
divisible by four, S₄, and the actual prime-subfield PGL₂(p) embeddings.
The ambient two-part excludes A₄ and A₅. The PSL₂(p) alternative has even
index p(p²+1), so cannot contain the Sylow subgroup. Elementary, cyclic and
Borel groups are excluded by the noncyclic two-Sylow.

The last theorem applies this calculation to the literal canonical preimage
of an ambient PGL₂ Sylow overgroup. The subfield case retains Dickson's
conjugator and faithful coefficient-field representation. No exhaustion of
whole PGL₂ overgroups is asserted here.

Source: Huppert II.8.27 (Dickson), used for Aschbacher--Smith A.2.3(2) and
E.1.14(6), printed pp.33 and 214, citing Aschbacher (1982), Lemma 4.10.
-/

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups

open Subgroup GorensteinWalter
open PrimeGeometry.Diagonal.MaximalOvergroups

variable {F : Type*} [Field F] [Finite F]

open scoped Pointwise

omit [Field F] [Finite F] in
/-- Square degree satisfies the odd-prime-power convention without excluding p = 3 or 5. -/
public theorem oddPrimePower_of_square_card {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2) : IsOddPrimePower (Nat.card F) :=
  ⟨p, 2, Fact.out, hpodd, by decide, hFcard⟩

/-- Every odd square-degree PGL₂ has order divisible by sixteen. -/
public theorem sixteen_dvd_pgl_card {p : ℕ} (ho : Odd p)
    (hF : Nat.card F = p ^ 2) : 16 ∣ Nat.card (PGL2 F) := by
  have h8 : 8 ∣ Nat.card F - 1 := by
    rw [hF]
    exact Nat.eight_dvd_sq_sub_one_of_odd ho
  have h2 : 2 ∣ Nat.card F + 1 := by
    have hq : Odd (Nat.card F) := hF ▸ ho.pow
    obtain ⟨k, hk⟩ := hq
    exact ⟨k + 1, by omega⟩
  have h16 : 16 ∣ Nat.card F ^ 2 - 1 := by
    have he : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      simpa using Nat.sq_sub_sq (Nat.card F) 1
    rw [he]
    exact Nat.mul_dvd_mul h2 h8
  rw [pgl2_card_formula]
  exact dvd_mul_of_dvd_right h16 _

/-- Every odd square-degree PSL₂ has order divisible by eight. -/
public theorem eight_dvd_psl_card {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hF : Nat.card F = p ^ 2) : 8 ∣ Nat.card (PSL2 F) := by
  have hd := sixteen_dvd_pgl_card ho hF
  rw [pgl2_card_formula] at hd
  rw [psl2_card_formula F (oddPrimePower_of_square_card ho hF)]
  obtain ⟨k, hk⟩ := hd
  exact ⟨k, by omega⟩

private theorem not_prime_psl_model {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (S : Sylow 2 (PSL2 F)) (H : Subgroup (PSL2 F))
    (hSH : (S : Subgroup _) ≤ H)
    (e : H ≃* PSL2 (GaloisField p 1)) : False := by
  let K := GaloisField p 1
  have hp : p.Prime := Fact.out
  have hpc : Nat.card K = p := by
    simpa only [K, pow_one] using GaloisField.card p 1 (by decide)
  have hK : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hpodd, le_rfl, by simpa using hpc⟩
  have hF := oddPrimePower_of_square_card hpodd hFcard
  have hHc : Nat.card H = p * (p ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, psl2_card_formula K hK, hpc]
  have hFc : Nat.card (PSL2 F) = p ^ 2 * ((p ^ 2) ^ 2 - 1) / 2 := by
    rw [psl2_card_formula F hF, hFcard]
  have heven : 2 ∣ p * (p ^ 2 - 1) :=
    dvd_mul_of_dvd_right ((show 2 ∣ 8 by decide).trans
      (Nat.eight_dvd_sq_sub_one_of_odd hpodd)) p
  have hHmul : 2 * Nat.card H = p * (p ^ 2 - 1) := by
    rw [hHc, Nat.mul_div_cancel' heven]
  have hFmul : 2 * Nat.card (PSL2 F) = p ^ 2 * ((p ^ 2) ^ 2 - 1) := by
    have hd := sixteen_dvd_pgl_card hpodd hFcard
    rw [pgl2_card_formula, hFcard] at hd
    rw [hFc, Nat.mul_div_cancel' ((show 2 ∣ 16 by decide).trans hd)]
  have hsplit : (p ^ 2) ^ 2 - 1 = (p ^ 2 - 1) * (p ^ 2 + 1) := by
    simpa [Nat.mul_comm] using Nat.sq_sub_sq (p ^ 2) 1
  have hfac : Nat.card (PSL2 F) = Nat.card H * (p * (p ^ 2 + 1)) := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    calc
      2 * Nat.card (PSL2 F) = p ^ 2 * ((p ^ 2 - 1) * (p ^ 2 + 1)) := by
        rw [hFmul, hsplit]
      _ = (p * (p ^ 2 - 1)) * (p * (p ^ 2 + 1)) := by ring
      _ = 2 * (Nat.card H * (p * (p ^ 2 + 1))) := by rw [← hHmul]; ring
  have hi : H.index = p * (p ^ 2 + 1) :=
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H))
      (H.card_mul_index.trans hfac)
  have h2 : 2 ∣ H.index := by
    rw [hi]
    apply dvd_mul_of_dvd_right
    obtain ⟨k, hk⟩ := hpodd.pow (n := 2)
    exact ⟨k + 1, by omega⟩
  exact S.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hSH))

/-- A proper PSL₂ Sylow overgroup is split dihedral, S₄, or a marked prime-subfield PGL₂. -/
public theorem square_psl_sylow_overgroup_cases {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (S : Sylow 2 (PSL2 F)) (H : Subgroup (PSL2 F))
    (hSH : (S : Subgroup _) ≤ H) (hH : H ≠ ⊤) :
    (∃ z : ℕ, 4 ∣ z ∧ z ∣ (Nat.card F - 1) / 2 ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
    (Nonempty (H ≃* PGL2 (GaloisField p 1)) ∧
      Nonempty (Glauberman.Dickson.SubfieldConjugacyWitness p 1 H)) := by
  classical
  have hF := oddPrimePower_of_square_card hpodd hFcard
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
    obtain ⟨a, ha⟩ := hpodd.pow (n := 2)
    exact ⟨a, by omega⟩
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
  · obtain ⟨z, hz, hc, he⟩ := hDihedral
    have h8H : 8 ∣ Nat.card H := (S.pow_dvd_card_of_pow_dvd_card
      (show 2 ^ 3 ∣ Nat.card (PSL2 F) from eight_dvd_psl_card hpodd hFcard)).trans
        (Subgroup.card_dvd_of_le hSH)
    have h4z : 4 ∣ z := by
      rw [hc] at h8H
      exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h8H
    have hzsplit : z ∣ (Nat.card F - 1) / 2 := by
      rcases hz with hz | hz
      · simpa only [hgcd] using hz
      · have h4 : 4 ∣ (Nat.card F + 1) / 2 :=
          h4z.trans (by simpa only [hgcd] using hz)
        obtain ⟨k, hk⟩ := Nat.eight_dvd_sq_sub_one_of_odd hpodd
        rw [hFcard] at h4
        have hp0 : 0 < p ^ 2 := by rw [← hFcard]; exact Nat.card_pos
        obtain ⟨a, ha⟩ := h4
        omega
    exact Or.inl ⟨z, h4z, hzsplit, hc, he⟩
  · exfalso
    obtain ⟨e⟩ := hA4.2
    have hc : Nat.card H = 12 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hd := (S.pow_dvd_card_of_pow_dvd_card
      (show 2 ^ 3 ∣ Nat.card (PSL2 F) from eight_dvd_psl_card hpodd hFcard)).trans
        (Subgroup.card_dvd_of_le hSH)
    norm_num [hc] at hd
  · exact Or.inr (Or.inl hS4.2)
  · exfalso
    obtain ⟨e⟩ := hA5.2
    have hc : Nat.card H = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hd := (S.pow_dvd_card_of_pow_dvd_card
      (show 2 ^ 3 ∣ Nat.card (PSL2 F) from eight_dvd_psl_card hpodd hFcard)).trans
        (Subgroup.card_dvd_of_le hSH)
    norm_num [hc] at hd
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
    obtain ⟨m, _hm0, hmdiv, ⟨eH⟩, _hw⟩ := hPSL
    rcases (Nat.dvd_prime Nat.prime_two).mp hmdiv with hm | hm
    · subst m
      exact not_prime_psl_model hpodd hFcard S H hSH eH
    · subst m
      let K := GaloisField p 2
      have hKcard : Nat.card K = Nat.card F := by
        simpa only [K, hFcard] using GaloisField.card p 2 (by decide)
      have hK : IsOddPrimePower (Nat.card K) := hKcard ▸ hF
      apply hH (Subgroup.eq_top_of_card_eq (H := H) ?_)
      calc
        Nat.card H = Nat.card (PSL2 K) := Nat.card_congr eH.toEquiv
        _ = Nat.card (PSL2 F) := by
          rw [psl2_card_formula K hK, psl2_card_formula F hF, hKcard]
  · obtain ⟨m, hm0, hmdiv, eH, hw⟩ := hPGL
    have hm : m = 1 := by
      have hle : 2 * m ≤ 2 := Nat.le_of_dvd (by decide) hmdiv
      omega
    subst m
    exact Or.inr (Or.inr ⟨eH, hw⟩)

/-- Apply the square-degree exhaustion to the literal canonical inner intersection. -/
public theorem inner_square_dickson_cases {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hTM : (T : Subgroup _) ≤ M) (hM : M ≠ ⊤) :
    (∃ z : ℕ, 4 ∣ z ∧ z ∣ (Nat.card F - 1) / 2 ∧
      Nat.card (inner M) = 2 * z ∧ Nonempty (inner M ≃* DihedralGroup z)) ∨
    Nonempty (inner M ≃* Equiv.Perm (Fin 4)) ∨
    (Nonempty (inner M ≃* PGL2 (GaloisField p 1)) ∧
      Nonempty (Glauberman.Dickson.SubfieldConjugacyWitness p 1 (inner M))) := by
  have hF := oddPrimePower_of_square_card hpodd hFcard
  obtain ⟨S, hS⟩ := exists_sylow_le_inner hF T M hTM
  exact square_psl_sylow_overgroup_cases hpodd hFcard S (inner M) hS
    (inner_ne_top hF T M hTM hM)


end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups
