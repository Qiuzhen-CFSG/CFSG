module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ResidualPrimitive
public import Theory.GroupTheory.PResidual.Restriction

/-!
# Original local residuals inside the universal normal base

Intersecting a finite local group with the ambient two-residual does not
change its own two-residual. Functoriality places the local residual in the
intersection, and the existing residual restriction theorem identifies its
embedded residual with the original one. The ambient completion need not be
finite. Transport through the universal marked endpoint maps then identifies
each local residual in the actual normal base with its original finite
endpoint residual.

These equivalences transfer the exclusions of the cubic and alternating-four
cases to Goldschmidt's two-perfect tree action without transferring a bound
on the original overlap to its residual. Source: Goldschmidt, *Automorphisms
of trivalent graphs* (1980), (3.2) and the reduction in (4.1)--(4.2),
printed pp.386--387 and 392--393.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private def localIntersectionEquiv (F : Bool → Subgroup G) (i : Bool) :
    residualFamily F i ≃* (pResidual 2 G).subgroupOf (F i) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  map_mul' _ _ := rfl

private def residualEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    pResidual 2 H ≃* pResidual 2 K :=
  (e.subgroupMap (pResidual 2 H)).trans (MulEquiv.subgroupCongr (map_pResidual 2 e))

/-- The local residual is unchanged when the cubic action is restricted to
its ambient two-residual. The ambient completion itself can be infinite. -/
noncomputable def CubicTreeAction.residualLocalEquiv (h : CubicTreeAction F) (i : Bool) :
    pResidual 2 (residualFamily F i) ≃* pResidual 2 (F i) := by
  let : Finite (F i) := h.finite i
  let D := (pResidual 2 G).subgroupOf (F i)
  have htop : (pResidual 2 (⊤ : Subgroup (F i))).map
      (⊤ : Subgroup (F i)).subtype = pResidual 2 (F i) :=
    map_pResidual 2 Subgroup.topEquiv
  have hD : (pResidual 2 (F i)) ≤ D := by
    intro x hx
    exact map_pResidual_le 2 (F i).subtype (mem_map_of_mem _ hx)
  have hmap : (pResidual 2 D).map D.subtype = pResidual 2 (F i) := by
    exact (embedded_pResidual_eq_of_le_of_residual_le 2
      (show D ≤ ⊤ from le_top) (htop.symm ▸ hD)).trans htop
  exact (residualEquiv (localIntersectionEquiv F i)).trans
    (((pResidual 2 D).equivMapOfInjective D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap))

open RankTwoAmalgam

/-- The left local residual in the actual universal normal base is isomorphic
to the residual of the original finite left endpoint. -/
noncomputable def universalResidualLeftEquiv [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥) :
    pResidual 2 (residualFamily (Universal.cosetFamily (inclusionAmalgam A B)) false) ≃*
      pResidual 2 A := by
  let u := Universal.markedIso (inclusionAmalgam A B)
    (Subgroup.inclusion_injective inf_le_left) (Subgroup.inclusion_injective inf_le_right)
  exact ((universalCubicTreeAction_of_goldschmidt h hcore).residualLocalEquiv false).trans
    (residualEquiv u.left.symm)

/-- The corresponding right endpoint identification retains the original
universal embedding before restricting to its two-residual. -/
noncomputable def universalResidualRightEquiv [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥) :
    pResidual 2 (residualFamily (Universal.cosetFamily (inclusionAmalgam A B)) true) ≃*
      pResidual 2 B := by
  let u := Universal.markedIso (inclusionAmalgam A B)
    (Subgroup.inclusion_injective inf_le_left) (Subgroup.inclusion_injective inf_le_right)
  exact ((universalCubicTreeAction_of_goldschmidt h hcore).residualLocalEquiv true).trans
    (residualEquiv u.right.symm)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
