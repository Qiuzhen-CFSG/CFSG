module
public import Stellmacher.ElementaryAbelianMaxJMap
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors.Prime
public import CFSG.Quasithin.ChapterB.Section02.BaumannFrattini
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup

/-!
# Solvable three-prime central-seed fusion

Solvable Thompson factorization would supply an SL₂(2) factor if the
Thompson subgroup moved a reduced elementary two-subgroup. Its order six
is impossible in a three-prime group. For a central Sylow seed in a
characteristic-two overgroup, the resulting centralization gives a
Frattini factorization over the Baumann normalizer. Every conjugate of a
subgroup of the seed is therefore already realized by that normalizer.

Source: Aschbacher–Smith, B.2.14–16 and the application in 5.1.17,
printed p.640 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]
theorem thompson_centralizes_reduced_of_solvable_three_prime
    (U : Subgroup G) (hr : IsPReduced 2 U)
    (hs : Group.IsSolvable G) (h3 : ¬ 3 ∣ Nat.card G) (T : Sylow 2 G) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G) := by
  let : U.Normal := hr.normal
  let : IsElementaryAbelian 2 U := hr.elementary
  let : Group.IsSolvable G := hs
  by_contra hn
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  obtain ⟨d,_,_,_,_⟩ := thompson_factors_of_solvable_action U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) T hn
    inferInstance hr.quotient_pCore_eq_bot
  let i : Fin d.count := ⟨0,d.count_pos⟩
  have hc : Nat.card (d.factor i) = 6 := by
    have e := (d.factorModel i).trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  exact h3 ((show 3 ∣ Nat.card (d.factor i) by rw [hc]; decide).trans
    ((card_subgroup_dvd_card (d.factor i)).trans (card_quotient_dvd_card _)))

theorem solvable_three_prime_central_seed_factorization
    (T : Sylow 2 G) (M Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hTM : (T : Subgroup G) ≤ M) (hZT : Z ≤ (T : Subgroup G))
    (hZC : Z ≤ centralizer (T : Set G))
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hs : Group.IsSolvable M) (h3 : ¬ 3 ∣ Nat.card M) :
    M = (M ⊓ centralizer (conjugateSpanBy Z M : Set G)) ⊔
      (M ⊓ normalizer (baumann (T : Subgroup G) : Set G)) := by
  let U := conjugateSpanBy Z M
  have hUM : U ≤ M := conjugateSpanBy_le (hZT.trans hTM) M.le_normalizer
  have hr : IsPReduced 2 (U.subgroupOf M) :=
    reduced_conjugateSpan_of_sylow_central T M Z hTM hZT hZC hchar
  let : IsElementaryAbelian 2 (U.subgroupOf M) := hr.elementary
  let : (U.subgroupOf M).Normal := hr.normal
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUM).symm.toMonoidHom (subgroupOfEquivOfLe hUM).symm.injective
  have ht := thompson_centralizes_reduced_of_solvable_three_prime
    (U.subgroupOf M) hr hs h3 (T.subtype hTM)
  have hm := map_mono (f := M.subtype) ht
  rw [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM,map_centralizer_subtype,
    map_subgroupOf_eq_of_le hUM] at hm
  have hf := BaumannFrattini.centralizing_characteristic_factorization
    T M U hTM hUM hm (⊤ : Subgroup (baumann (T : Subgroup G)))
  simpa only [← MonoidHom.range_eq_map,range_subtype] using hf

open scoped Pointwise
/-- Conjugation on any subgroup of the central seed is already realized in
its Baumann normalizer. -/
theorem solvable_three_prime_central_seed_fusion
    (T : Sylow 2 G) (M Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hTM : (T : Subgroup G) ≤ M) (hZT : Z ≤ (T : Subgroup G))
    (hZC : Z ≤ centralizer (T : Set G))
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hs : Group.IsSolvable M) (h3 : ¬ 3 ∣ Nat.card M)
    (Z₁ : Subgroup G) (hZZ : Z₁ ≤ Z) {g : G} (hg : g ∈ M) :
    ∃ b ∈ M ⊓ normalizer (baumann (T : Subgroup G) : Set G),
      Z₁.map (MulAut.conj g).toMonoidHom = Z₁.map (MulAut.conj b).toMonoidHom := by
  let U := conjugateSpanBy Z M
  let C := M ⊓ centralizer (U : Set G)
  let B := M ⊓ normalizer (baumann (T : Subgroup G) : Set G)
  have hMC : M ≤ normalizer (C : Set G) :=
    (le_inf M.le_normalizer ((le_normalizer_conjugateSpanBy Z M).trans
      (normalizer_le_normalizer_centralizer U))).trans inf_normalizer_le_normalizer_inf
  have hf : M = B ⊔ C := by
    rw [sup_comm]
    exact solvable_three_prime_central_seed_factorization T M Z hTM hZT hZC hchar hs h3
  have hp : g ∈ (B : Set G) * (C : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right B C (inf_le_left.trans hMC), ← hf]
    exact hg
  obtain ⟨b,hb,c,hc,rfl⟩ := hp
  refine ⟨b,hb,?_⟩
  have he : Z₁.map (MulAut.conj c).toMonoidHom = Z₁ := by
    have hzfix (z : G) (hz : z ∈ Z₁) : (MulAut.conj c) z = z := by
      change c * z * c⁻¹ = z
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hc.2 z
        (hZZ.trans (le_conjugateSpanBy Z M) hz)).symm
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      change (MulAut.conj c) z ∈ Z₁
      rw [hzfix z hz]
      exact hz
    · intro z hz
      exact ⟨z,hz,hzfix z hz⟩
  have hm : (MulAut.conj (b * c)).toMonoidHom =
      (MulAut.conj b).toMonoidHom.comp (MulAut.conj c).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [hm,← map_map,he]
end CFSG.Quasithin.ChapterB
