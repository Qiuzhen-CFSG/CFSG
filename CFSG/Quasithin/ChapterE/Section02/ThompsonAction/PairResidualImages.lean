module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualFactors
/-!
# Alternating axes of the original paired symmetric-five residuals

Transport the two actual factor residuals through the original quotient map
and the same marked product. The two-residual of each symmetric-five factor
is its alternating subgroup, so their literal images are the two A5 axes.
Together with `paired_residual_factors_generate`, these are the component
identities used in E.2.3 and the componentwise C.1.24 span argument.

Source: Aschbacher--Smith E.2.3(3), pp.216--217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

private theorem five_axis_left_residual :
    (pResidual 2 ((⊤ : Subgroup S5).prod (⊥ : Subgroup S5))).map
      ((⊤ : Subgroup S5).prod (⊥ : Subgroup S5)).subtype = (A5).prod ⊥ := by
  let A := (⊤ : Subgroup S5).prod (⊥ : Subgroup S5)
  let e : S5 ≃* A := {
    toFun := fun g => ⟨(g,1),⟨mem_top _,one_mem _⟩⟩
    invFun := fun g => g.1.1
    left_inv := fun _ => rfl
    right_inv := fun g => Subtype.ext (Prod.ext rfl (by simpa only [mem_bot] using g.property.2.symm))
    map_mul' := fun _ _ => Subtype.ext (Prod.ext rfl (one_mul 1).symm) }
  rw [← map_pResidual 2 e,Equiv.Perm.twoResidual_eq_alternating,Subgroup.map_map]
  ext x
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨hg,one_mem _⟩
  · rintro ⟨h₁,h₂⟩
    refine ⟨x.1,h₁,Prod.ext rfl ?_⟩
    exact h₂.symm

private theorem five_axis_right_residual :
    (pResidual 2 ((⊥ : Subgroup S5).prod (⊤ : Subgroup S5))).map
      ((⊥ : Subgroup S5).prod (⊤ : Subgroup S5)).subtype = (⊥ : Subgroup S5).prod A5 := by
  let A := (⊥ : Subgroup S5).prod (⊤ : Subgroup S5)
  let e : S5 ≃* A := {
    toFun := fun g => ⟨(1,g),⟨one_mem _,mem_top _⟩⟩
    invFun := fun g => g.1.2
    left_inv := fun _ => rfl
    right_inv := fun g => Subtype.ext (Prod.ext (by simpa only [mem_bot] using g.property.1.symm) rfl)
    map_mul' := fun _ _ => Subtype.ext (Prod.ext (one_mul 1).symm rfl) }
  rw [← map_pResidual 2 e,Equiv.Perm.twoResidual_eq_alternating,Subgroup.map_map]
  ext x
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨one_mem _,hg⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨x.2,h₂,Prod.ext h₁.symm rfl⟩

variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) H V) (q : G →* H) (hq : Function.Surjective q)
  (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
  (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))

include hq in
theorem paired_symmetric_first_residual_image :
    (factorResidual q (offenderSubgroup ρ) d.first).map q =
      ((A5).prod (⊥ : Subgroup S5)).map
        ((offenderSubgroup ρ).subtype.comp c.action.groupEquiv.symm.toMonoidHom) := by
  rw [factorResidual_image q hq,← c.first_eq,← map_embedded_pResidual,five_axis_left_residual,
    Subgroup.map_map]

include hq in
theorem paired_symmetric_second_residual_image :
    (factorResidual q (offenderSubgroup ρ) d.second).map q =
      ((⊥ : Subgroup S5).prod A5).map
        ((offenderSubgroup ρ).subtype.comp c.action.groupEquiv.symm.toMonoidHom) := by
  rw [factorResidual_image q hq,← c.second_eq,← map_embedded_pResidual,five_axis_right_residual,
    Subgroup.map_map]
end CFSG.Quasithin.ChapterE.ThompsonAction
