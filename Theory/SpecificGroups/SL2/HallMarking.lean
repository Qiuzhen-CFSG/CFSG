module
public import Theory.SpecificGroups.SL2.OddBorelMarking
public import Theory.GroupTheory.Hall.TwoClosedNormal
/-!
# Full diagonal coordinates on odd Hall subgroups

A marked Sylow normalizer splits as its Sylow two-subgroup times an odd
Hall subgroup. If that Hall subgroup is marked diagonally in an SL₂ pair,
its two diagonal characters are jointly surjective: lift an arbitrary
diagonal pair and compare the diagonal entries in the Sylow/Hall factorization.
The original quotient map and the common marking are retained.

Source: the full invariant Cartan subgroup in Aschbacher--Smith, 10.2.3,
printed p.745, before the field-factor elimination.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {A F : Type*} [Group A] [Finite A] [Field F]

theorem pair_hall_marking_surjective
    (q : A →* (SL(2,F) × SL(2,F))) (hq : Function.Surjective q)
    (S : Sylow 2 A) (hk : q.ker ≤ (S : Subgroup A))
    (hS : (S : Subgroup A).map q = (upperUnipotent F).prod (upperUnipotent F))
    (C : Subgroup A)
    (hHall : IsHallSubgroup OddHall.oddPrimes (C.subgroupOf (normalizer (S : Set A))))
    (d : C →* Fˣ × Fˣ)
    (hd : ∀ x : C, q x = (diag2 ((d x).1 : F) (Units.ne_zero _),
      diag2 ((d x).2 : F) (Units.ne_zero _))) : Function.Surjective d := by
  intro z
  let D := (diag2 (z.1 : F) z.1.ne_zero,diag2 (z.2 : F) z.2.ne_zero)
  have hDN : D ∈ normalizer (((upperUnipotent F).prod (upperUnipotent F)) : Set _) := by
    apply mem_normalizer_iff.mpr
    intro y
    exact and_congr
      (mem_normalizer_iff.mp (diag_mem_rankOneBorel (z.1 : F) z.1.ne_zero) y.1)
      (mem_normalizer_iff.mp (diag_mem_rankOneBorel (z.2 : F) z.2.ne_zero) y.2)
  obtain ⟨x,hx⟩ := hq D
  have hxN : x ∈ normalizer (S : Set A) := by
    have he : (normalizer (((S : Subgroup A).map q) : Set _)).comap q =
        normalizer (S : Set A) := by
      rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hk,S.coe_coe]
    rw [←he]
    change q x ∈ normalizer (((S : Subgroup A).map q) : Set _)
    rw [hS,hx]
    exact hDN
  let N := normalizer (S : Set A)
  let SN : Sylow 2 N := S.subtype (by simpa only [S.coe_coe] using (S : Subgroup A).le_normalizer)
  obtain ⟨⟨s,c⟩,hsc⟩ := (OddHall.sylow_complement_of_hall SN hHall).2 ⟨x,hxN⟩
  let c' : C := ⟨c.val.val,c.property⟩
  refine ⟨c',?_⟩
  have hs : q s.val.val ∈ (upperUnipotent F).prod (upperUnipotent F) := by
    rw [←hS]
    exact mem_map_of_mem q s.property
  obtain ⟨u,hu⟩ := (mem_upperUnipotent F _).mp hs.1
  obtain ⟨v,hv⟩ := (mem_upperUnipotent F _).mp hs.2
  have he : q s.val.val * q c' = D := by
    rw [←map_mul]
    exact (congrArg q (congrArg Subtype.val hsc)).trans hx
  rw [hd] at he
  have h1 := congrArg (fun g : SL(2,F) × SL(2,F) => g.1.val 0 0) he
  have h2 := congrArg (fun g : SL(2,F) × SL(2,F) => g.2.val 0 0) he
  apply Prod.ext <;> apply Units.ext
  · change ((q s.val.val).1 * diag2 ((d c').1 : F) (Units.ne_zero _)).val 0 0 = _ at h1
    rw [←hu] at h1
    simpa [D,mul_apply,Fin.sum_univ_two,transvection_coe,diag2_coe'] using h1
  · change ((q s.val.val).2 * diag2 ((d c').2 : F) (Units.ne_zero _)).val 0 0 = _ at h2
    rw [←hv] at h2
    simpa [D,mul_apply,Fin.sum_univ_two,transvection_coe,diag2_coe'] using h2
end Matrix.SpecialLinearGroup
