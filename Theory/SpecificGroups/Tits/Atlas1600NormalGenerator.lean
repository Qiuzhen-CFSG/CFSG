module

public import Theory.SpecificGroups.Tits.Atlas1600R5
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A normal generator for the concrete Atlas group

The Parrott word `r₅ = s₁ s₅²` normally generates the concrete permutation
image. In any quotient killing this word, relations (VII) and (VIII) kill
`r₃` and `s₁`; relation (VI) then kills `r₁`, the first Atlas generator.
The orders three and thirteen of `b` and `ab` kill the second generator.

The Parrott relations come from Parrott (1972), §5, p. 683. The final Atlas
permutation identity is checked pointwise by Lean against the supplied
`refs/original/n-group-global/atlas-tits-p1600-{a,b}.g` data.
-/

namespace Tits

private theorem r1_eq_one_of_r5_eq_one {G : Type*} [Group G] (g : ParrottGenerator → G)
    (hg : SatisfiesParrottRelations g) (hz : g .s1 * g .s5 ^ 2 = 1) :
    g .r1 = 1 := by
  have cancel (a x : G) (ha : a * a = 1) (hx : a * x * a = 1) : x = 1 := by
    have h : a * x * a = a * 1 * a := by simpa only [mul_one] using hx.trans ha.symm
    exact mul_left_cancel (mul_right_cancel h)
  have h8 := hg .i_r8
  have h3 := hg .viii_r3
  have h7 := hg .vii_r3
  have h1 := hg .viii_s1
  have h5 := hg .vi_s1_r1
  have h2 := hg .i_r1
  simp only [parrottRelator, parrottR3, parrottR5, parrottR7,
    map_mul, map_inv, map_pow, FreeGroup.lift_apply_of] at h3 h7 h1 h5 h2 h8
  have hr3 : g .s1 * g .s2 * g .s3 ^ 2 = 1 := by
    apply cancel (g .r8) _ (by simpa only [pow_two] using h8)
    simpa only [hz, inv_one, mul_one] using h3
  have hprod := (mul_inv_eq_one.mp h7).symm
  simp only [hr3, mul_one, ← pow_two, h2] at hprod
  have hs1 : g .s1 = 1 := by
    apply cancel (g .r8) _ (by simpa only [pow_two] using h8)
    simpa only [hr3, hprod, inv_one, mul_one] using h1
  rw [hs1, one_mul] at h5
  have heq : g .r1 ^ 5 = g .r1 := by
    calc
      g .r1 ^ 5 = (g .r1 ^ 2) ^ 2 * g .r1 := by
        simp only [← pow_mul, ← pow_succ]
      _ = g .r1 := by rw [h2]; simp
  exact heq.symm.trans h5

private theorem atlas1600AB_pow_thirteen :
    (atlas1600A * atlas1600B) ^ 13 = 1 := by
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  set_option maxRecDepth 20000 in
    set_option maxHeartbeats 16000000 in
      decide +kernel

private theorem atlas1600B_pow_three : atlas1600B ^ 3 = 1 := by
  apply Equiv.ext
  intro x
  exact atlas1600BMap_cube x

/-- Every normal subgroup containing `r₅` contains both Atlas generators. -/
public theorem atlas1600_normal_eq_top_of_r5_mem
    (N : Subgroup Atlas1600Group) [N.Normal] (hz : atlas1600R5 ∈ N) : N = ⊤ := by
  let q := QuotientGroup.mk' N
  let g := fun i => q (atlas1600ParrottAssignment i)
  have hg : SatisfiesParrottRelations g := by
    have hl : FreeGroup.lift g = q.comp (FreeGroup.lift atlas1600ParrottAssignment) := by
      ext i
      simp [g]
    intro i
    rw [hl, MonoidHom.comp_apply, atlas1600ParrottAssignment_relations i, map_one]
  have hz' : g .s1 * g .s5 ^ 2 = 1 := by
    have h := (QuotientGroup.eq_one_iff atlas1600R5).mpr hz
    change q atlas1600R5 = 1 at h
    simpa only [atlas1600R5_eq, map_mul, map_pow] using h
  let a : Atlas1600Group := ⟨atlas1600A, atlas1600A_mem⟩
  let b : Atlas1600Group := ⟨atlas1600B, atlas1600B_mem⟩
  have ha : q a = 1 := by
    have h := r1_eq_one_of_r5_eq_one g hg hz'
    have heq : a = atlas1600ParrottAssignment .r1 := by
      apply Subtype.ext
      change atlas1600A = (atlas1600ParrottAssignment .r1).val
      rw [atlas1600ParrottAssignment_val]
      exact Atlas1600ParrottData.atlasA_word
    exact heq.symm ▸ h
  have hb3 : q b ^ 3 = 1 := by
    rw [← map_pow]
    have h : b ^ 3 = 1 := Subtype.ext atlas1600B_pow_three
    rw [h, map_one]
  have hb13 : q b ^ 13 = 1 := by
    have h : (a * b) ^ 13 = 1 := Subtype.ext atlas1600AB_pow_thirteen
    have hh := congrArg q h
    simpa only [map_pow, map_mul, ha, one_mul, map_one] using hh
  have hb : q b = 1 := by
    have heq : q b ^ 13 = q b := by
      calc
        q b ^ 13 = (q b ^ 3) ^ 4 * q b := by
          simp only [← pow_mul, ← pow_succ]
        _ = q b := by rw [hb3]; simp
    exact heq.symm.trans hb13
  have hle : atlas1600Subgroup ≤ N.map atlas1600Subgroup.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro x (rfl | hx)
    · exact ⟨a, (QuotientGroup.eq_one_iff a).mp ha, rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨b, (QuotientGroup.eq_one_iff b).mp hb, rfl⟩
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hy, hxy⟩ := hle x.property
  exact (Subtype.ext hxy : y = x) ▸ hy

/-- The concrete central word is a normal generator of the Atlas image. -/
public theorem atlas1600R5_normalClosure :
    Subgroup.normalClosure ({atlas1600R5} : Set Atlas1600Group) = ⊤ :=
  atlas1600_normal_eq_top_of_r5_mem _
    (Subgroup.subset_normalClosure (Set.mem_singleton _))

end Tits
