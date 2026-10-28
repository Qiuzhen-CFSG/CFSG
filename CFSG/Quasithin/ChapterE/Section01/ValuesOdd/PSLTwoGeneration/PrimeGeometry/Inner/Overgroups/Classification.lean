module

public import GorensteinWalter.PSL2Cardinality
public import GorensteinWalter.KleinFourExceptionTransport
import Glauberman.DicksonClassification
import Mathlib.Tactic

/-!
# Four-group overgroups in prime-field PSL₂

Dickson's classification leaves precisely the even dihedral, A₄, S₄ and A₅
models for a proper subgroup containing a four-group. The odd elementary
kernel in the elementary-by-cyclic case meets the four-group trivially, so
its cyclic quotient excludes that case. For a prime field, the PSL₂ subfield
case has the whole ambient order, and the PGL₂ subfield degree is impossible.
The proof uses actual subgroup isomorphisms and does not assume simplicity.

Source: Huppert II.8.27, as proved in `Glauberman.DicksonClassification`;
the overgroup calculation used for Aschbacher--Smith E.1.14(6), printed p.214.
-/

public section

open Subgroup GorensteinWalter
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

private theorem no_four_in_odd_by_cyclic {K : Type*} [Group K] [Finite K]
    (A N C : Subgroup K) (hA : IsKleinFour A) (hN : N.Normal)
    (hNo : Odd (Nat.card N)) (hC : IsCyclic C)
    (hdisj : Disjoint N C) (hjoin : N ⊔ C = ⊤) : False := by
  let := hN
  have hcomp : N.IsComplement' C := by
    refine ⟨Subgroup.mul_injective_of_disjoint hdisj, ?_⟩
    intro g
    have hg : g ∈ (N : Set K) * (C : Set K) := by
      rw [← Subgroup.normal_mul N C, hjoin]
      trivial
    rcases hg with ⟨n, hn, c, hc, hnc⟩
    exact ⟨⟨⟨n, hn⟩, ⟨c, hc⟩⟩, hnc⟩
  let : IsCyclic (K ⧸ N) := hcomp.symm.QuotientMulEquiv.isCyclic.mpr hC
  have hcop : Nat.Coprime (Nat.card A) (Nat.card N) := by
    rw [hA.card_four]
    exact (Nat.coprime_two_left.mpr hNo).pow_left 2
  have hinf : A ⊓ N = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  let q : A →* K ⧸ N := (QuotientGroup.mk' N).comp A.subtype
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    apply le_bot_iff.mp
    intro x hx
    have hxN : (x : K) ∈ N := (QuotientGroup.eq_one_iff (N := N) _).mp hx
    have hxbot : (x : K) ∈ (⊥ : Subgroup K) := hinf ▸ ⟨x.property, hxN⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  exact @IsKleinFour.not_isCyclic A _ hA (isCyclic_of_injective q hq)

private theorem model_proper_overgroup_models {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hF : Nat.card F = p)
    (A M : Subgroup (PSL2 F)) (hA : IsKleinFour A) (hAM : A ≤ M) (hM : M ≠ ⊤) :
    (∃ k : ℕ, 0 < k ∧ Nonempty (M ≃* DihedralGroup (2 * k))) ∨
      Nonempty (M ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (M ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (M ≃* alternatingGroup (Fin 5)) := by
  classical
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := p) (f := 1) (by simpa using hF) M with
    helem | hcyc | hdih | h4 | hs | h5 | hsemi | hpsl | hpgl
  · exact (no_kleinFour_of_pGroup_subgroup M A
      (IsElementaryAbelian.isPGroup p M) hpodd hAM hA).elim
  · exact (no_kleinFour_subgroup_of_isCyclic M A hA hAM hcyc.choose_spec.2.2).elim
  · obtain ⟨n, _, hc, eM⟩ := hdih
    have hn : 0 < n := by
      have hpos := Nat.card_pos (α := M)
      rw [hc] at hpos
      omega
    have heven : Even n := by
      rcases Nat.even_or_odd n with h | h
      · exact h
      · exact (no_kleinFour_subgroup_of_dihedral_odd M A n hA hAM eM h).elim
    obtain ⟨k, hk⟩ := heven
    have heq : n = 2 * k := by omega
    exact Or.inl ⟨k, by omega, heq ▸ eM⟩
  · exact Or.inr (Or.inl h4.2)
  · exact Or.inr (Or.inr (Or.inl hs.2))
  · exact Or.inr (Or.inr (Or.inr h5.2))
  · obtain ⟨m, t, _, _, N, C, hn, _, hnc, hcc, _, hd, hj⟩ := hsemi
    have hno : Odd (Nat.card N) := by rw [hnc]; exact hpodd.pow
    exact (no_four_in_odd_by_cyclic (A.subgroupOf M) N C
      (isKleinFour_subgroupOf hAM hA) hn hno hcc hd hj).elim
  · obtain ⟨m, _, hm, ⟨eM⟩⟩ := hpsl
    have hm1 : m = 1 := Nat.eq_one_of_dvd_one hm
    subst m
    have hK : Nat.card (GaloisField p 1) = p := by
      simpa using GaloisField.card p 1 (by decide)
    have hFo : IsOddPrimePower (Nat.card F) :=
      ⟨p, 1, Fact.out, hpodd, le_rfl, by simpa using hF⟩
    have hKo : IsOddPrimePower (Nat.card (GaloisField p 1)) :=
      ⟨p, 1, Fact.out, hpodd, le_rfl, by simpa using hK⟩
    apply (hM (Subgroup.eq_top_of_card_eq M ?_)).elim
    rw [Nat.card_congr eM.toEquiv, psl2_card_formula _ hKo,
      psl2_card_formula _ hFo, hK, hF]
  · obtain ⟨m, _, hm, _⟩ := hpgl
    have := Nat.eq_one_of_dvd_one hm
    omega

omit [Finite G] in
/-- A proper prime-field PSL₂ overgroup of a four-group has one of the four
actual Dickson models. The dihedral rotation parameter is positive and even. -/
theorem proper_overgroup_models {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hF : Nat.card F = p) (e : G ≃* PSL2 F)
    (A M : Subgroup G) (hA : IsKleinFour A) (hAM : A ≤ M) (hM : M ≠ ⊤) :
    (∃ k : ℕ, 0 < k ∧ Nonempty (M ≃* DihedralGroup (2 * k))) ∨
      Nonempty (M ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (M ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (M ≃* alternatingGroup (Fin 5)) := by
  let A' := A.map e.toMonoidHom
  let M' := M.map e.toMonoidHom
  let eM : M ≃* M' := M.equivMapOfInjective e.toMonoidHom e.injective
  have hM' : M' ≠ ⊤ := by
    intro h
    apply hM
    apply top_unique
    intro x _
    have hx : e x ∈ M' := by rw [h]; trivial
    obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp hx
    exact e.injective he ▸ hy
  rcases model_proper_overgroup_models hpodd hF A' M'
      (isKleinFour_map_mulEquiv_cross A hA e) (Subgroup.map_mono hAM) hM' with
    ⟨k, hk, ⟨ek⟩⟩ | h4 | hs | h5
  · exact Or.inl ⟨k, hk, ⟨eM.trans ek⟩⟩
  · exact Or.inr (Or.inl ⟨eM.trans h4.some⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨eM.trans hs.some⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨eM.trans h5.some⟩))
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups
