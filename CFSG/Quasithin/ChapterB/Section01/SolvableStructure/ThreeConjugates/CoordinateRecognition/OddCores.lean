module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Choices
public import Theory.PPrimeCore
public import Mathlib.GroupTheory.IndexNormal
/-!
# Odd cores of the concrete factors

A subgroup of order three in a group of order six has index two, hence
is normal and equals the odd core. Each concrete factor has order six,
so its included odd core has order three. Independence distinguishes these
cores, and their characteristic property transports them under the literal
ambient conjugation maps. No individual factor is assumed ambient normal.

Source: Aschbacher–Smith, B.1.12, printed p. 73 (PDF p. 84).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors

private theorem oddCore_card_le_three {H : Type*} [Group H] [Finite H]
    (hc : Nat.card H = 6) : Nat.card (pPrimeCore 2 H) ≤ 3 := by
  have hd := (pPrimeCore 2 H).card_subgroup_dvd_card
  rw [hc] at hd
  exact Nat.le_of_dvd (by decide)
    ((pPrimeCore_coprime_card (p := 2) (G := H)).symm.dvd_of_dvd_mul_left
      (show Nat.card (pPrimeCore 2 H) ∣ 2 * 3 from hd))

private theorem three_eq_oddCore {H : Type*} [Group H] [Finite H]
    (hc : Nat.card H = 6) (K : Subgroup H) (hK : Nat.card K = 3) :
    K = pPrimeCore 2 H := by
  have hi : K.index = 2 := by
    have := K.card_mul_index
    rw [hK, hc] at this
    omega
  have hn := K.normal_of_index_eq_two hi
  have hle : K ≤ pPrimeCore 2 H := le_sSup ⟨hn, by rw [hK]; decide⟩
  exact eq_of_le_of_card_ge hle (by rw [hK]; exact oddCore_card_le_three hc)

private theorem oddCore_card_of_six {H : Type*} [Group H] [Finite H]
    (hc : Nat.card H = 6) : Nat.card (pPrimeCore 2 H) = 3 := by
  let R : Sylow 3 H := default
  have hR : Nat.card R = 3 := by
    rw [R.card_eq_multiplicity, hc]
    rw [show (6 : ℕ) = 3 * 2 from rfl,
      Nat.factorization_mul (by decide) (by decide),
      Nat.prime_three.factorization, Nat.prime_two.factorization]
    norm_num
  rw [← three_eq_oddCore hc (R : Subgroup H) hR]
  exact hR

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

/-- The intrinsic odd core of a factor, included by its literal subtype. -/
def factorOddCore (i : Fin d.count) : Subgroup G :=
  (pPrimeCore 2 (d.factor i)).map (d.factor i).subtype

omit [Finite G] in
theorem factorOddCore_le (i : Fin d.count) : d.factorOddCore i ≤ d.factor i := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem factorOddCore_card (i : Fin d.count) : Nat.card (d.factorOddCore i) = 3 := by
  rw [factorOddCore, card_map_of_injective (d.factor i).subtype_injective]
  exact oddCore_card_of_six (d.factor_card i)

theorem factorOddCore_ne_bot (i : Fin d.count) : d.factorOddCore i ≠ ⊥ := by
  intro h
  have := d.factorOddCore_card i
  rw [h, card_bot] at this
  omega

theorem eq_factorOddCore_of_card_three {K : Subgroup G}
    (hK : Nat.card K = 3) {i : Fin d.count} (hle : K ≤ d.factor i) :
    K = d.factorOddCore i := by
  have hc : Nat.card (K.subgroupOf (d.factor i)) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hK
  have he := three_eq_oddCore (d.factor_card i) (K.subgroupOf (d.factor i)) hc
  have := congrArg (Subgroup.map (d.factor i).subtype) he
  simpa only [map_subgroupOf_eq_of_le hle, factorOddCore] using this

theorem factorOddCore_injective : Function.Injective d.factorOddCore := by
  intro i j he
  by_contra hij
  have hd := (d.factors_independent.pairwiseDisjoint hij).mono
    (d.factorOddCore_le i) (d.factorOddCore_le j)
  rw [he, disjoint_self] at hd
  exact d.factorOddCore_ne_bot j hd

omit [Finite G] in
theorem factorOddCore_map_conj (g : G) {i j : Fin d.count}
    (h : (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j) :
    (d.factorOddCore i).map (MulAut.conj g).toMonoidHom = d.factorOddCore j := by
  let e : d.factor i ≃* d.factor j :=
    ((MulAut.conj g).subgroupMap (d.factor i)).trans (MulEquiv.subgroupCongr h)
  have he : (d.factor j).subtype.comp e.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (d.factor i).subtype := by
    ext x
    rfl
  rw [factorOddCore, map_map, ← he, ← map_map, pPrimeCore_map_iso]
  rfl

theorem factor_map_conj_of_oddCore (hperm : ∀ (g : G) (i : Fin d.count),
      ∃ j, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j)
    (g : G) {i j : Fin d.count}
    (h : (d.factorOddCore i).map (MulAut.conj g).toMonoidHom = d.factorOddCore j) :
    (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j := by
  obtain ⟨k, hk⟩ := hperm g i
  have he := (d.factorOddCore_map_conj g hk).symm.trans h
  exact d.factorOddCore_injective he ▸ hk

/-- A nontrivial coordinate core cannot lie in a subproduct omitting it. -/
theorem mem_of_factorOddCore_le_subproduct (I : Set (Fin d.count)) {i : Fin d.count}
    (hle : d.factorOddCore i ≤ ⨆ j ∈ I, d.factor j) : i ∈ I := by
  by_contra hi
  have hd := (d.factors_independent.disjoint_biSup hi).mono (d.factorOddCore_le i) hle
  exact d.factorOddCore_ne_bot i (disjoint_self.mp hd)

end CFSG.Quasithin.ChapterB.SolvableFFFactors
