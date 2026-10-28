module
public import Theory.GroupTheory.NormalSymmetricThree
public import Theory.GroupTheory.OddPrimeSectionCentralizers.SymmetricThree

/-!
# A symmetric-three pair quotient killing a normal symmetric-three subgroup

A normal S₃ splits off its centralizer. If a surjection onto S₃² kills
that subgroup, its restriction to the centralizer is still surjective,
and the split projection supplies a surjection onto S₃³. A group of
three-rank at most two cannot cover this group. The rank hypothesis stays
on the original covering group, with no condition on the quotient kernel.

Source: Aschbacher--Smith 15.1.2, printed p.1085, using A.1.31(1).
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThree
variable {A B : Type*} [Group A] [Group B] [Finite B]
local notation "S3" => Equiv.Perm (Fin 3)

theorem exists_cube_surjection (H : Subgroup A) [H.Normal]
    (j : H ≃* S3) (q : A →* S3 × S3) (hq : Function.Surjective q)
    (hH : H ≤ q.ker) :
    ∃ r : A →* S3 × (S3 × S3), Function.Surjective r := by
  obtain ⟨e,he⟩ := exists_product_equiv H j
  let C := centralizer (H : Set A)
  let qC : C →* S3 × S3 := q.comp C.subtype
  have hqC : Function.Surjective qC := by
    intro y
    obtain ⟨a,ha⟩ := hq y
    refine ⟨(e.symm a).2,?_⟩
    have hh : q ((e.symm a).1 : A) = 1 := hH (e.symm a).1.property
    have hx := congrArg q (he (e.symm a).1 (e.symm a).2)
    rw [e.apply_symm_apply,map_mul,hh,one_mul] at hx
    exact hx.symm.trans ha
  let r := (MonoidHom.prodMap j.toMonoidHom qC).comp e.symm.toMonoidHom
  refine ⟨r,?_⟩
  intro y
  obtain ⟨c,hc⟩ := hqC y.2
  refine ⟨e (j.symm y.1,c),?_⟩
  change (j (e.symm (e (j.symm y.1,c))).1,qC (e.symm (e (j.symm y.1,c))).2) = y
  rw [e.symm_apply_apply,j.apply_symm_apply,hc]

theorem not_surjective_pair_killing_normal_symmetricThree
    (hrank : primeRank 3 B ≤ 2) (f : B →* A) (hf : Function.Surjective f)
    (H : Subgroup A) [H.Normal] (j : H ≃* S3)
    (q : A →* S3 × S3) (hq : Function.Surjective q) (hH : H ≤ q.ker) : False := by
  obtain ⟨r,hr⟩ := exists_cube_surjection H j q hq hH
  exact not_surjective_symmetricThreeCube_of_threeRank_le_two hrank
    (r.comp f) (hr.comp hf)
end Theory.GroupTheory.NormalSymmetricThree
