module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M23.Orders
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M23.Seven
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M22
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Transport
public import Theory.Mathieu.M23.Properties.OuterRestriction

/-!
# The Cartan restriction for the actual M₂₃ automorphism groups

The order bounds leave only the cyclic Cartan orders seven and fifteen.
In the seven case the odd abelian overgroup has order seven, and its product
with the Sylow fixes a natural point. Restricting the complete witness to
that point stabilizer gives the already proved M₂₂ bound. The fifteen case
is excluded by the native Sylow-five congruence. The proved outer two-group
restriction then covers all automorphism subgroups containing the inner group.

Source: Aschbacher--Smith, Definition E.3.37 and Proposition 7.3.4,
printed pp.239 and 699.
-/

public section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models
open Subgroup Sporadic.Mathieu
open scoped Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

private theorem sylow_card (S : Sylow 2 M23) : Nat.card S = 128 := by
  rw [Sylow.card_eq_multiplicity, m23_order]
  decide +kernel

private theorem product_card {c : ℕ} (w : NPrimeWitness M23 c) :
    Nat.card (w.abelianGroup ⊔ (w.sylow : Subgroup M23) : Subgroup M23) =
      Nat.card w.abelianGroup * 128 := by
  have hs := sylow_card w.sylow
  have hd : Disjoint w.abelianGroup (w.sylow : Subgroup M23) := by
    apply disjoint_of_coprime_natCard
    rw [hs]
    exact (Nat.coprime_two_right.mpr w.odd).pow_right 7
  have hprod := card_set_mul_mul_card_inf w.abelianGroup (w.sylow : Subgroup M23)
  rw [hd.eq_bot, Subgroup.card_bot, mul_one,
    ← coe_sup_of_set_mul_comm _ _ w.permutes, hs] at hprod
  exact hprod

private theorem bound_of_seven {c : ℕ} (w : NPrimeWitness M23 c)
    (h7 : 7 ∣ Nat.card w.abelianGroup) : c ≤ 2 := by
  let := w.abelian
  let H := w.abelianGroup ⊔ (w.sylow : Subgroup M23)
  have hcard : Nat.card H = 896 := by
    rw [product_card w, M23Cartan.abelian_seven_card w.abelianGroup w.odd h7]
  obtain ⟨a,ha⟩ := M23Cartan.seven_overgroup_preserves_point H w.sylow le_sup_right hcard
  let v := ParabolicCartan.MarkedModels.restrictWitness w (MulAction.stabilizer M23 a)
    (le_sup_left.trans ha) (le_sup_right.trans ha)
  let : MulAction.IsPretransitive M23 (Fin 23) := m23_isPretransitive
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23 (9 : Fin 23) a
  let e : MulAction.stabilizer M23 a ≃* M22 :=
    (MulAction.stabilizerEquivStabilizer hg.symm).symm.trans m23EquivM22PointStabilizer.symm
  exact (v.map e.toMonoidHom e.surjective
    (e.injective.comp v.cyclicGroup.subtype_injective)).le_nPrime.trans m22_nPrime_le_two

private theorem no_fifteen {c : ℕ} (w : NPrimeWitness M23 c) :
    Nat.card w.cyclicGroup ≠ 15 := by
  intro h15
  let := w.abelian
  let := w.cyclic
  have hd : 15 ∣ Nat.card w.abelianGroup := h15 ▸ card_dvd_of_le w.cyclic_le
  have hB : Nat.card w.abelianGroup = 15 := by
    rcases M23Cartan.abelian_five_card w.abelianGroup w.odd ((by decide : 5 ∣ 15).trans hd) with h | h
    · rw [h] at hd
      norm_num at hd
    · exact h
  let H := w.abelianGroup ⊔ (w.sylow : Subgroup M23)
  have hcard : Nat.card H = 1920 := by rw [product_card w, hB]
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := w.cyclicGroup)
  let f : w.cyclicGroup →* H := Subgroup.inclusion (w.cyclic_le.trans le_sup_left)
  exact M23Cartan.no_fifteen_overgroup H hcard (f x)
    ((orderOf_injective f (Subgroup.inclusion_injective _) x).trans (hx.trans h15))

theorem m23_nPrime_le_two : nPrime M23 ≤ 2 := by
  apply nPrime_le_iff.mpr
  intro c w
  have hcy : 2 ^ c - 1 ∣ 10200960 := by
    rw [← w.card, ← m23_order]
    exact w.cyclicGroup.card_subgroup_dvd_card
  have hc : c < 24 := by
    by_contra h
    have hp : 2 ^ 24 ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) (by omega)
    have hl := Nat.le_of_dvd (by norm_num : 0 < 10200960) hcy
    norm_num at hp
    omega
  have h7cy : 7 ∣ 2 ^ c - 1 → c ≤ 2 := fun h => bound_of_seven w
    ((show 7 ∣ Nat.card w.cyclicGroup by simpa only [w.card] using h).trans
      (card_dvd_of_le w.cyclic_le))
  have h15 := no_fifteen w
  have hcard := w.card
  interval_cases c <;> omega

/-- Every inner-containing automorphism subgroup of the actual M₂₃ has Cartan parameter at most two. -/
theorem m23_cartanRestriction (A : Subgroup (MulAut M23))
    (hA : MulAut.innerSubgroup M23 ≤ A) : nPrime A ≤ 2 :=
  (automorphism_subgroup_nPrime_le
    (MulAut.conj_injective_of_center_eq_bot M23Geometry.m23_center_eq_bot)
    m23_outer_isTwoGroup A hA).trans m23_nPrime_le_two

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models
