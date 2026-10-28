module

public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrderCertificate
public import Theory.GroupTheory.PresentedGroupBounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# Order of the second Tits parabolic

The checked three-coset table gives the upper bound `3 * 2048`. The Sylow
subgroup and the element `r8 * s8` of order three give the reverse divisibility
bound. Thus the actual overgroup has order 6144. No two-core or quotient
identification is assumed in this calculation.

Recovered from the saved `qt-f-01-exceptional-tits-local` calculation
(workspace `5f870ea650214a13878958406fc30629`), preserving its proof.
Source: Parrott (1972), pp. 672 and 683; the concrete generators are those of
`Atlas1600Parrott`. The associated source correction is separated from the
positive order calculation.
-/

@[expose] public section

namespace Tits.RelativeSecondBlockLayers
open ExceptionalParabolics SecondOrder

private theorem val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
private theorem val_one : (1 : Atlas1600Group).val = 1 := rfl

private theorem s_mem (i : ParrottGenerator) (hi : i ≠ .r1) (hi8 : i ≠ .r8) :
    atlas1600ParrottAssignment i ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  apply Subgroup.subset_closure
  cases i <;> simp_all

private theorem generator_mem (a : Fin 9) : generator a ∈ second := by
  fin_cases a
  · exact reflection_mem_second
  all_goals apply sylow_le_second; apply s_mem <;> decide

private theorem generates : Subgroup.closure (Set.range generator) = second := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨a, rfl⟩
    exact generator_mem a
  · apply sup_le
    · rw [S, atlas1600SylowTwoSubgroup_eq]
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨8, rfl⟩
      · exact ⟨7, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
    · apply (Subgroup.closure_le _).mpr
      rintro x (rfl : x = atlas1600ParrottAssignment .r8)
      exact Subgroup.subset_closure ⟨0, rfl⟩

private def gen (a : Fin 9) : second := ⟨generator a, generator_mem a⟩

private theorem gen_generates : Subgroup.closure (Set.range gen) = ⊤ := by
  apply top_unique
  intro x _
  let H := Subgroup.closure (Set.range gen)
  have h : second ≤ H.map second.subtype := by
    conv_lhs => rw [← generates]
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨a, rfl⟩
    exact ⟨gen a, Subgroup.subset_closure ⟨a, rfl⟩, rfl⟩
  obtain ⟨y, hy, hxy⟩ := h x.property
  have heq : y = x := Subtype.ext hxy
  exact heq ▸ hy

private theorem rep_mem (i : Fin 3) : rep i ∈ second := by
  apply Subgroup.pow_mem
  exact second.mul_mem (sylow_le_second (s_mem .s8 (by decide) (by decide)))
    reflection_mem_second

private def cover : Subgroup.GeneratorCosetCover (S.subgroupOf second) gen (Fin 3) where
  repr i := ⟨rep i, rep_mem i⟩
  initial := 0
  initial_eq := by apply Subtype.ext; exact pow_zero _
  step i a := by
    refine ⟨⟨⟨atlas1600SylowTwoNormalForm (factor a i),
      sylow_le_second (atlas1600SylowTwoNormalForm_mem _)⟩,
      atlas1600SylowTwoNormalForm_mem _⟩, dest a i, ?_⟩
    exact Subtype.ext (step a i)
  inv_step i a := by
    let j := destInverse a i
    let n := factor a j
    refine ⟨⟨⟨(atlas1600SylowTwoNormalForm n)⁻¹,
      second.inv_mem (sylow_le_second (atlas1600SylowTwoNormalForm_mem _))⟩,
      S.inv_mem (atlas1600SylowTwoNormalForm_mem _)⟩, j, ?_⟩
    apply Subtype.ext
    change rep i * (generator a)⁻¹ = (atlas1600SylowTwoNormalForm n)⁻¹ * rep j
    have h : rep j * generator a = atlas1600SylowTwoNormalForm n * rep i := by
      simpa only [j, n, dest_inverse] using step a (destInverse a i)
    calc
      rep i * (generator a)⁻¹ = (atlas1600SylowTwoNormalForm n)⁻¹ *
          (rep j * generator a) * (generator a)⁻¹ := by rw [h]; group
      _ = (atlas1600SylowTwoNormalForm n)⁻¹ * rep j := by group

private theorem card_le : Nat.card second ≤ 6144 := by
  have h := (cover.finite_card_le gen_generates).2
  have hs : Nat.card (S.subgroupOf second) = 2048 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylow_le_second).toEquiv).trans sylow_card
  simpa only [hs, Nat.card_fin] using h

private theorem rotation_order :
    orderOf (atlas1600ParrottAssignment .r8 * atlas1600ParrottAssignment .s8) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · simpa [parrottRelator] using atlas1600ParrottAssignment_relations .vi_r8_s8
  · intro h
    have hpoint := congrArg (fun x : Atlas1600Group => x.val 0) h
    simp only [val_mul, val_one, atlas1600ParrottAssignment_val,
      Atlas1600ParrottData.permutation, Equiv.Perm.one_apply] at hpoint
    change (Atlas1600ParrottData.r8Perm * Atlas1600ParrottData.s8Perm) 0 = 0 at hpoint
    have : (Atlas1600ParrottData.r8Perm * Atlas1600ParrottData.s8Perm) 0 ≠ 0 := by
      decide +kernel
    exact this hpoint

theorem second_card : Nat.card second = 6144 := by
  have hs : 2048 ∣ Nat.card second := by
    rw [← sylow_card]
    exact Subgroup.card_dvd_of_le sylow_le_second
  have h3 : 3 ∣ Nat.card second := by
    rw [← rotation_order]
    exact second.orderOf_dvd_natCard
      (second.mul_mem reflection_mem_second
        (sylow_le_second (s_mem .s8 (by decide) (by decide))))
  have hd : 6144 ∣ Nat.card second :=
    (show Nat.Coprime 2048 3 by decide).mul_dvd_of_dvd_of_dvd hs h3
  have hp : 0 < Nat.card second := Nat.card_pos
  have hl := Nat.le_of_dvd hp hd
  exact Nat.le_antisymm card_le hl

/-- The specified three-coset normal forms in the actual second parabolic. -/
def secondNormalForm (p : Fin 2048 × Fin 3) : second :=
  ⟨atlas1600SylowTwoNormalForm p.1 * SecondOrder.rep p.2,
    second.mul_mem (sylow_le_second (atlas1600SylowTwoNormalForm_mem _)) (by exact rep_mem _)⟩

@[simp] theorem secondNormalForm_val (p : Fin 2048 × Fin 3) :
    (secondNormalForm p).val = atlas1600SylowTwoNormalForm p.1 * SecondOrder.rep p.2 := rfl

/-- Every second-parabolic element is a Sylow word times one of the three representatives. -/
theorem secondNormalForm_surjective : Function.Surjective secondNormalForm := by
  intro x
  obtain ⟨s, i, hx⟩ := cover.covers gen_generates x
  obtain ⟨n, hn⟩ := atlas1600SylowTwoNormalForm_surjective s.property
  refine ⟨(n, i), Subtype.ext ?_⟩
  change atlas1600SylowTwoNormalForm n * SecondOrder.rep i = x.val
  rw [hn]
  exact (congrArg Subtype.val hx).symm

/-- The three-coset normal forms are unique, as their number equals the proved order. -/
theorem secondNormalForm_bijective : Function.Bijective secondNormalForm :=
  secondNormalForm_surjective.bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_fin, Nat.card_fin, second_card])

/-- The ambient Sylow marking restricts to the second parabolic. -/
def secondSylowTwo : Sylow 2 second :=
  atlas1600SylowTwo.subtype (by simpa only [atlas1600SylowTwo_coe] using sylow_le_second)

theorem secondSylowTwo_coe :
    (secondSylowTwo : Subgroup second) = S.subgroupOf second := by
  rw [secondSylowTwo, Sylow.coe_subtype, atlas1600SylowTwo_coe]

/-- Its relative index is three. -/
theorem second_sylow_index : (S.subgroupOf second).index = 3 := by
  have hs : Nat.card (S.subgroupOf second) = 2048 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylow_le_second).toEquiv).trans sylow_card
  have h := (S.subgroupOf second).card_mul_index
  rw [hs, second_card] at h
  omega

end Tits.RelativeSecondBlockLayers
