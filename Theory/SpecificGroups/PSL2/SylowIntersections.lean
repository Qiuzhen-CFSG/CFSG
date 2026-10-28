module

public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.GroupTheory.SylowCentralizerTransport

/-!
# Binary linear Sylow intersections

The upper root subgroup is an actual Sylow subgroup, and its nonidentity
elements have that root subgroup as centralizer. Transport and the Sylow
centralizer argument prove that distinct Sylow two-subgroups intersect
trivially. No simplicity or lower field bound is needed.

Source: the rank-one geometry used in Aschbacher--Smith 2.5.3(3), p.552.
-/

public section
namespace Theory.PSL2
open Subgroup BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem sylow_eq_of_inf_ne_bot (P Q : Sylow 2 (PSL2MatrixGroup F))
    (hi : (P : Subgroup (PSL2MatrixGroup F)) ⊓ (Q : Subgroup (PSL2MatrixGroup F)) ≠ ⊥) : P = Q := by
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow F 2
  let R := U.mapSurjective (f := pi F) pi_surjective
  have hR : (R : Subgroup (PSL2MatrixGroup F)) = PUnip F := by
    rw [Sylow.coe_mapSurjective]
    change (Matrix.SpecialLinearGroup.upperUnipotent F).map (pi F) =
      (Unip F).map (pi F)
    congr 1
    ext g
    rw [Matrix.SpecialLinearGroup.mem_upperUnipotent, mem_Unip_iff]
    have ht (t : F) :
        Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t =
          uni t := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.transvection_coe]
    simp only [ht, eq_comm]
  apply Sylow.eq_of_inf_ne_bot_of_one_sylow R P Q _ hi
  rw [hR]
  rintro x ⟨u, hu, rfl⟩ hne
  obtain ⟨t, rfl⟩ := (mem_Unip_iff u).mp hu
  have ht : t ≠ 0 := by intro h; exact hne (by simp [h, uni_zero])
  exact (centralizer_root_eq ht).le

end Theory.PSL2
