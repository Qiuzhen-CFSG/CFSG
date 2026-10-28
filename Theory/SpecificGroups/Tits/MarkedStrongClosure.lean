module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.LongRoot

/-!
# Noncommuting returning conjugates of a two-central Tits involution

The proved root marking identifies every nonidentity Sylow-central element
of Parrott's group with the class of s₁. Its conjugate by the INTERNAL
generator r₈ is s₇r₇, a word in the eight generators of the derived Sylow.
The two words do not commute: their products send point zero to different
points of the faithful degree-1600 permutation representation. Only this
single point is checked; no involution or multiplication table is enumerated.

Sylow conjugacy puts the pair inside the original marked Sylow. The carrier
is ParrottGroup, identified with the derived binary Ree group by the imported
root-marked comparison. The full fixed group ²F₄(2) is kept distinct.

Source: Parrott (1972), §5, p.683; Aschbacher--Smith 1.1.5(3)(a), pp.501--503,
and Proposition 2.2.2, pp.519--520, combined 1 March 2004 manuscript.
-/

public section
noncomputable section
open Subgroup
namespace Tits.MarkedStrongClosure
open InvolutionRootGeometry

private def standardSylow : Sylow 2 ParrottGroup :=
  atlas1600SylowTwo.mapSurjective (f := parrottFiniteImageEquiv.symm.toMonoidHom)
    parrottFiniteImageEquiv.symm.surjective

private theorem generator_mem_standard (i : ParrottGenerator)
    (hr1 : i ≠ .r1) (hr8 : i ≠ .r8) : parrottGenerator i ∈ standardSylow := by
  refine ⟨atlas1600ParrottAssignment i, ?_, ?_⟩
  · change atlas1600ParrottAssignment i ∈ (atlas1600SylowTwo : Subgroup Atlas1600Group)
    rw [atlas1600SylowTwo_coe, atlas1600SylowTwoSubgroup_eq]
    apply Subgroup.subset_closure
    cases i <;> simp_all
  · change parrottFiniteImageEquiv.symm (atlas1600ParrottAssignment i) = parrottGenerator i
    rw [← parrottFiniteImageEquiv_generator]
    exact parrottFiniteImageEquiv.symm_apply_apply _

private theorem r8_inv : (parrottGenerator .r8)⁻¹ = parrottGenerator .r8 := by
  have hs : parrottGenerator .r8 ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using
      parrott_generators_satisfy_relations .i_r8
  exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)

private def second : ParrottGroup :=
  parrottGenerator .r8 * parrottGenerator .s1 * (parrottGenerator .r8)⁻¹

private theorem second_eq_word :
    second = parrottGenerator .s7 *
      (parrottGenerator .s1 * parrottGenerator .s2 * parrottGenerator .s3 ^ 2 *
        parrottGenerator .s3 * parrottGenerator .s5 * parrottGenerator .s7) := by
  have h := parrott_generators_satisfy_relations .viii_s1
  simp only [parrottRelator, parrottR7, parrottR3, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of] at h
  simpa only [second, r8_inv] using mul_inv_eq_one.mp h

private theorem second_mem_standard : second ∈ standardSylow := by
  rw [second_eq_word]
  let S : Subgroup ParrottGroup := standardSylow
  have h1 : parrottGenerator .s1 ∈ S := generator_mem_standard .s1 (by decide) (by decide)
  have h2 : parrottGenerator .s2 ∈ S := generator_mem_standard .s2 (by decide) (by decide)
  have h3 : parrottGenerator .s3 ∈ S := generator_mem_standard .s3 (by decide) (by decide)
  have h5 : parrottGenerator .s5 ∈ S := generator_mem_standard .s5 (by decide) (by decide)
  have h7 : parrottGenerator .s7 ∈ S := generator_mem_standard .s7 (by decide) (by decide)
  exact S.mul_mem h7 (S.mul_mem (S.mul_mem (S.mul_mem
    (S.mul_mem (S.mul_mem h1 h2) (S.pow_mem h3 2)) h3) h5) h7)

/-- A single faithful point distinguishes the two products. The actual
values are 1569 and 863, in zero-based point numbering. -/
private theorem point_noncommutation :
    (Atlas1600ParrottData.s1Perm *
      (Atlas1600ParrottData.r8Perm * Atlas1600ParrottData.s1Perm *
        Atlas1600ParrottData.r8Perm)) (0 : Fin 1600) ≠
    ((Atlas1600ParrottData.r8Perm * Atlas1600ParrottData.s1Perm *
      Atlas1600ParrottData.r8Perm) * Atlas1600ParrottData.s1Perm) (0 : Fin 1600) := by
  decide +kernel

private theorem pair_not_commute : ¬Commute (parrottGenerator .s1) second := by
  intro hc
  have h := hc.eq
  simp only [second, r8_inv] at h
  have he := congrArg parrottFiniteImageEquiv h
  simp only [map_mul, parrottFiniteImageEquiv_generator] at he
  have hm := congrArg (fun x : Atlas1600Group => x.val) he
  have val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
  simp only [val_mul, atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation] at hm
  exact point_noncommutation (congrArg (fun p : Equiv.Perm (Fin 1600) => p 0) hm)

/-- Every marked Sylow contains two noncommuting conjugates of its actual
central involution. All conjugators are internal to the simple Tits group. -/
theorem sylow_noncommuting_conjugates (R : Sylow 2 ParrottGroup) (v : ParrottGroup)
    (hvR : v ∈ R) (hv : orderOf v = 2) (hc : ∀ x ∈ R, Commute v x) :
    ∃ a b : R, IsConj v (a : ParrottGroup) ∧ IsConj v (b : ParrottGroup) ∧
      ¬Commute a b := by
  have hvn : v ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hv
    norm_num at hv
  have hvC : v ∈ centralizer (R : Set ParrottGroup) := by
    exact mem_centralizer_iff.mpr (fun x hx => (hc x hx).symm.eq)
  have hclass : IsConj v (parrottGenerator .s1) :=
    ((isLongRoot_iff v).mp ((isLongRoot_iff_twoCentral v).mpr ⟨hvn, R, hvR, hvC⟩)).symm
  have hsecond : IsConj (parrottGenerator .s1) second :=
    isConj_iff.mpr ⟨parrottGenerator .r8, rfl⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ParrottGroup standardSylow R
  let f := MulAut.conj g
  have hm : (standardSylow : Subgroup ParrottGroup).map f.toMonoidHom =
      (R : Subgroup ParrottGroup) := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    exact hh
  let a : R := ⟨f (parrottGenerator .s1), by
    change f (parrottGenerator .s1) ∈ (R : Subgroup ParrottGroup)
    rw [← hm]
    exact mem_map_of_mem f.toMonoidHom
      (generator_mem_standard .s1 (by decide) (by decide))⟩
  let b : R := ⟨f second, by
    change f second ∈ (R : Subgroup ParrottGroup)
    rw [← hm]
    exact mem_map_of_mem f.toMonoidHom second_mem_standard⟩
  refine ⟨a, b, hclass.trans (isConj_iff.mpr ⟨g, rfl⟩),
    (hclass.trans hsecond).trans (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
  intro hab
  apply pair_not_commute
  apply f.injective
  have hh : (a : ParrottGroup) * (b : ParrottGroup) =
      (b : ParrottGroup) * (a : ParrottGroup) := congrArg Subtype.val hab.eq
  exact (f.map_mul _ _).trans (hh.trans (f.map_mul _ _).symm)

end Tits.MarkedStrongClosure
