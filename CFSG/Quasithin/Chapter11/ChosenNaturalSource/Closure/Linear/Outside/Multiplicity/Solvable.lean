module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Odd
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Transport
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Nonsolvable
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable

/-!
# Solvability of the original selected outside subgroup

The original H-action kernel lies in the solvable minimal-parabolic core.
The image of O²(H) lies in the abelian multiplicity image of C. Hence O²(H)
is solvable, and its two-group quotient makes H solvable. This supplies the
solvability premise of B.6.8(2) for the original H, rather than postulating
an odd residual quotient or replacing H by a model.

Source: Aschbacher--Smith, 11.5.7, printed p.782; B.6.8(2),(5),(6).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- The two source images centralize one another in the original quotient action. -/
theorem residual_image_centralizes_X₁ (hCG : C E ≤ E.G₁)
    (hab : IsMulCommutative (quotientAction E (C E) hCG).range) :
    ((outsideResidual E).subgroupOf (C E)).map (quotientAction E (C E) hCG) ≤
      centralizer (((X₁ E).subgroupOf (C E)).map (quotientAction E (C E) hCG) :
        Set (MulAut (E.W ⧸ E.V₁.subgroupOf E.W))) := by
  intro a ha
  apply mem_centralizer_iff.mpr
  intro b hb
  exact (congrArg (fun x : (quotientAction E (C E) hCG).range => x.val)
    ((isMulCommutative_iff.mp hab)
      ⟨a,map_le_range _ _ ha⟩ ⟨b,map_le_range _ _ hb⟩)).symm

/-- B.6.8 supplies solvability of the literal action kernel in H. -/
theorem H_action_kernel_solvable
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hNT : normalizer (T : Set G) ≤ E.M) :
    Group.IsSolvable (actionCentralizer E E.H hHG) := by
  obtain ⟨hmin,hker⟩ := H_action_kernel_le_core E hH hHG hNT
  let := ChapterB.minimalParabolic_core_solvable (T.subtype hH.1.1.2) hmin
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hker)

/-- An abelian actual C-image forces solvability of the selected H. -/
theorem H_solvable_of_image_commutative
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (hNT : normalizer (T : Set G) ≤ E.M)
    (hab : IsMulCommutative (quotientAction E (C E)
      (C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG)).range) :
    Group.IsSolvable E.H := by
  let α := quotientAction E E.H hHG
  let β := quotientAction E (C E)
    (C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG)
  let R := pResidual 2 E.H
  let f := α.comp R.subtype
  let i : R →* C E := (E.H.subtype.comp R.subtype).codRestrict (C E)
    (fun r => mem_sup_left (mem_sup_right (mem_map_of_mem E.H.subtype r.property)))
  have hfi : f = β.comp i := by
    ext r w
    dsimp only [f, α, β, MonoidHom.comp_apply]
    rw [quotientAction_restrict E E.H hHG,
      quotientAction_restrict E (C E)
        (C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG)]
    rfl
  let : Group.IsSolvable β.range := Group.isSolvable_of_comm (isMulCommutative_iff.mp hab)
  have hrange : f.range ≤ β.range := by
    rw [hfi, MonoidHom.range_comp]
    exact map_le_range _ _
  let : Group.IsSolvable f.range :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hrange)
  let : Group.IsSolvable α.ker := H_action_kernel_solvable E hH hHG hNT
  let j : f.ker →* α.ker := (R.subtype.comp f.ker.subtype).codRestrict α.ker
    (fun r => r.property)
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : α.ker => (x : E.H)) hab))
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  let : Group.IsSolvable R :=
    Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by
      intro r hr
      exact ⟨⟨r,congrArg Subtype.val hr⟩,rfl⟩)
  let : Group.IsNilpotent (E.H ⧸ R) := (isPGroup_quotient_pResidual 2).isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient R).mpr ⟨inferInstance,inferInstance⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
