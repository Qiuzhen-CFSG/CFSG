module

public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.Hall.NormalTwoCore
public import Mathlib.GroupTheory.Transfer

/-!
# The odd Hall transfer step of source Lemma 15.5

If the normalizer of each nontrivial subgroup of an odd Hall subgroup
centralizes that subgroup, primewise Burnside transfer makes the derived
group a two-group. Consequently the quotient by the two-core is abelian,
its Sylow two-subgroup is trivial, and the original odd Hall subgroup
complements the two-core. This is the normal-complement consequence used
for C₀ and its actual odd subgroup Y in GLS IV, Chapter 2, Lemma 15.5.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.OddSupplement
open Subgroup
open scoped commutatorElement IsMulCommutative

private theorem derived_two_of_oddHall_normalizers
    {H : Type*} [Group H] [Finite H] (Y : Subgroup H)
    (hy : IsHallSubgroup OddHall.oddPrimes Y)
    (hn : ∀ P : Subgroup H, P ≤ Y → P ≠ ⊥ →
      normalizer (P : Set H) ≤ centralizer (P : Set H)) :
    IsPGroup 2 (commutator H) := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpdiv := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p = 2 := by
    by_contra hne
    let : Fact p.Prime := ⟨hpprime⟩
    let P : Sylow p Y := Classical.choice inferInstance
    let B := (P : Subgroup Y).map Y.subtype
    have hBp : IsPGroup p B := P.isPGroup'.map _
    have hBY : B ≤ Y := map_subtype_le _
    have hBi : ¬ p ∣ B.index := by
      have hrelative : B.relIndex Y = (P : Subgroup Y).index := by
        change (B.subgroupOf Y).index = _
        congr 1
        exact comap_map_eq_self_of_injective Y.subtype_injective (P : Subgroup Y)
      have hi := relIndex_mul_index hBY
      intro hd
      rw [← hi, hrelative] at hd
      rcases hpprime.dvd_mul.mp hd with hd | hd
      · exact P.not_dvd_index hd
      · exact hy.p_in_pi_of_p_dvd_index ⟨p, hpprime⟩ hd hne
    let S : Sylow p H := hBp.toSylow hBi
    have hcentral : normalizer (S : Set H) ≤ centralizer (S : Set H) := by
      change normalizer (B : Set H) ≤ centralizer (B : Set H)
      by_cases hb : B = ⊥
      · intro g _ b hbmem
        have hb1 : b = 1 := mem_bot.mp (hb ▸ hbmem)
        simp only [hb1, one_mul, mul_one]
      · exact hn B hBY hb
    let f := MonoidHom.transferSylow S hcentral
    let : IsMulCommutative S := ⟨⟨fun a b => Subtype.ext
      (hcentral ((S : Subgroup H).le_normalizer b.property) a a.property)⟩⟩
    have hder : commutator H ≤ f.ker := by
      change ⁅(⊤ : Subgroup H), ⊤⁆ ≤ f.ker
      apply commutator_le.mpr
      intro x _ y _
      change f ⁅x,y⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    have hcomp := MonoidHom.ker_transferSylow_isComplement' S hcentral
    have hcop : ¬ p ∣ Nat.card f.ker := by
      change ¬ p ∣ Nat.card (MonoidHom.transferSylow S hcentral).ker
      rw [← hcomp.index_eq_card]
      exact S.not_dvd_index
    exact hcop (hpdiv.trans (card_dvd_of_le hder))
  simpa [hp2] using Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩

/-- Burnside transfer for the actual odd Hall subgroup; the returned
complement is the intrinsic two-core, with no solvability premise. -/
public theorem twoCore_complement_of_oddHall_normalizers
    {H : Type*} [Group H] [Finite H] (Y : Subgroup H)
    (hy : IsHallSubgroup OddHall.oddPrimes Y)
    (hn : ∀ P : Subgroup H, P ≤ Y → P ≠ ⊥ →
      normalizer (P : Set H) ≤ centralizer (P : Set H)) :
    (pCore 2 H).IsComplement' Y := by
  have hder : commutator H ≤ pCore 2 H :=
    le_sSup ⟨inferInstance, derived_two_of_oddHall_normalizers Y hy hn⟩
  let : IsMulCommutative (H ⧸ pCore 2 H) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hder
  let S : Sylow 2 H := Classical.choice inferInstance
  have hS := sylow_eq_core_of_commutative_quotient S
  exact hS ▸ OddHall.sylow_complement_of_hall S hy

end BenderSuzuki.ZD.LinearExclusion.OddSupplement
