module

public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.GroupTheory.UniqueMaximalNormalExtension
public import Theory.GroupTheory.SolvableRadical
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Nilpotent

/-!
# Borel uniqueness in perfect covers of SL₂

Let a finite perfect group A map onto SL₂(F), in characteristic two. If a
solvable normal subgroup R contains the kernel, the join of R with a Sylow
two-subgroup has a unique maximal overgroup. Its image is solvable and hence
proper in the nontrivial perfect image. Borel uniqueness therefore applies to
that image, and subgroup correspondence lifts the conclusion to A.

No field-size restriction is needed: the Borel calculation works over every
field, while perfectness supplies the nonsolvability required here.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.18, printed p.931, the minimal-parabolic deduction from a rank-one image.
-/

open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup

private theorem enlarge_unique {A : Type*} [Group A] [Finite A] {S T : Subgroup A}
    (h : Order.HasUniqueMaximalOver S ⊤) (hST : S ≤ T) (hT : T ≠ ⊤) :
    Order.HasUniqueMaximalOver T ⊤ := by
  obtain ⟨M, hM, hu⟩ := h.2
  refine ⟨lt_top_iff_ne_top.mpr hT, M,
    ⟨h.le_maximal hM hST (lt_top_iff_ne_top.mpr hT), hM.2⟩, ?_⟩
  intro N hN
  exact hu N ⟨hST.trans hN.1, hN.2⟩

/-- Borel uniqueness lifts to a perfect cover after adjoining any solvable
normal subgroup that contains the actual homomorphism kernel. -/
public theorem sylow_sup_solvable_hasUniqueMaximalOver_of_perfect_cover
    {A F : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    [Field F] [Finite F] [CharP F 2]
    (f : A →* SL(2, F)) (hf : Function.Surjective f)
    (R : Subgroup A) [R.Normal] [Group.IsSolvable R]
    (hk : f.ker ≤ R) (S : Sylow 2 A) :
    Order.HasUniqueMaximalOver ((S : Subgroup A) ⊔ R) ⊤ := by
  let : Group.IsPerfect SL(2, F) := Group.IsPerfect.ofSurjective hf
  let : Nontrivial SL(2, F) := by
    let t := transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F)
    refine ⟨⟨t, 1, ?_⟩⟩
    intro he
    have hh := congrArg (fun g : SL(2, F) => g.val 0 1) he
    simp [t, transvection_coe] at hh
  have hproper : (((S : Subgroup A) ⊔ R).map f) ≠ ⊤ := by
    intro he
    let N := R.map f
    let P := (S : Subgroup A).map f
    let : N.Normal := (inferInstance : R.Normal).map f hf
    let : Group.IsSolvable N := Group.isSolvable_of_surjective (f.subgroupMap_surjective R)
    let := S.isPGroup'.isNilpotent
    let : Group.IsSolvable P := Group.isSolvable_of_surjective
      (f.subgroupMap_surjective (S : Subgroup A))
    have hNP : N ⊔ P = ⊤ := by simpa only [Subgroup.map_sup, sup_comm] using he
    exact Group.IsPerfect.not_isSolvable SL(2, F)
      (Group.isSolvable_of_normal_sup_eq_top N P hNP)
  exact hasUniqueMaximalOver_of_surjective f hf (hk.trans le_sup_right)
    (enlarge_unique (sylow_hasUniqueMaximalOver 2 (S.mapSurjective hf))
      (map_mono le_sup_left) hproper)

end Matrix.SpecialLinearGroup
