module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage

/-!
# The original C-component in the literal star quotient

The core of a nonsolvable minimal parabolic is its solvable radical.
Thus every original C-component has nonabelian simple ordinary-component
image in H/J, including when the component is exchanged by the Sylow group.
Its generating relation passes through the same quotient homomorphism.
This supplies the literal carrier for the E.2.2 model dispatcher.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The actual original component becomes simple in H/J without a normality hypothesis. -/
theorem source_component_simple_image (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
    IsSimpleGroup (K.map q) ∧ IsComponent (H ⧸ ChapterB.minimalParabolicCore T hP) (K.map q) ∧
      ¬ IsMulCommutative (K.map q) ∧ K.map q ⊔ ((T : Subgroup H).map q) = ⊤ := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hJ := ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs
  have hrad : solvableRadical (H ⧸ J) = ⊥ := by
    let e : (H ⧸ J) ≃* (H ⧸ solvableRadical H) := QuotientGroup.quotientMulEquivOfEq hJ
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_solvableRadical_equiv,solvableRadical_quotient_solvableRadical,Subgroup.map_bot]
  have him := hK.map_quotient J
  have hc : IsComponent (H ⧸ J) (K.map q) :=
    (isCComponent_iff_isSubnormal_and_isQuasisimple_of_solvableRadical_eq_bot hrad).mp him
  refine ⟨him.isSimpleGroup_of_solvableRadical_eq_bot hrad,hc,
    him.not_isMulCommutative_of_solvableRadical_eq_bot hrad,?_⟩
  rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective J)]
end CFSG.Quasithin.ChapterE.Structure
