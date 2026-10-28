module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Source
public import Theory.Representation.BinaryOffender.EquivariantOffender
/-!
# Dual ratio estimates on invariant subspaces and subgroup actions

The dual restriction map is an equivariant surjection. Thus fixed
codimension and quadraticity descend to the dual of an invariant
subspace. A subactor inside a subgroup keeps its rank under literal
restriction, allowing the original rank budget to be used there.
Source: Aschbacher–Smith B.4.7 and C.5.13, printed pp.90 and162–163.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
omit [Finite H] in
/-- Dual fixed codimension decreases on invariant subspaces and subactors,
while literal restriction to a containing subgroup preserves actor rank. -/
theorem dual_restriction_estimates (ρ : Representation (ZMod 2) H W)
    (J : Subrepresentation ρ) (L A D : Subgroup H) (hDA : D ≤ A) (hDL : D ≤ L)
    (hquad : IsQuadratic ρ.dual A) :
    let σ : Representation (ZMod 2) L J.toSubmodule := J.toRepresentation.comp L.subtype
    IsQuadratic σ.dual (D.subgroupOf L) ∧
      fixedCodim σ.dual (D.subgroupOf L) ≤ fixedCodim ρ.dual A := by
  let f := J.toSubmodule.subtype.dualMap
  have hf : Function.Surjective f := LinearMap.dualMap_surjective_of_injective J.toSubmodule.subtype_injective
  have he (g : H) (w : Module.Dual (ZMod 2) W) :
      f (ρ.dual g w) = J.toRepresentation.dual g (f w) := rfl
  have hq := quadratic_of_equivariant_surjection ρ.dual J.toRepresentation.dual f hf he A hquad
  have hd : fixedCodim J.toRepresentation.dual D ≤ fixedCodim ρ.dual A := by
    apply (fixedCodim_le_of_equivariant_surjection ρ.dual J.toRepresentation.dual f hf he D).trans
    have hfix : fixedSpace ρ.dual A ≤ fixedSpace ρ.dual D := by
      intro v hv d
      exact hv ⟨d,hDA d.property⟩
    have hh := Submodule.finrank_mono hfix
    have ha := fixedCodim_add_finrank ρ.dual A
    have hd := fixedCodim_add_finrank ρ.dual D
    omega
  refine ⟨?_,?_⟩
  · intro a ha b hb v
    exact hq a (hDA ha) b (hDA hb) v
  · change fixedCodim (J.toRepresentation.dual.comp L.subtype) (D.subgroupOf L) ≤ _
    unfold fixedCodim
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hDL]
    exact hd
/-- A literal subactor with the source rank budget gives the ratio bound
on the dual of an invariant subspace, restricted to its containing group. -/
theorem dual_restriction_ratio (ρ : Representation (ZMod 2) H W)
    (J : Subrepresentation ρ) (L A D : Subgroup H) (hDA : D ≤ A) (hDL : D ≤ L)
    (hA : IsElementaryTwo A) (hD : D ≠ ⊥) (hquad : IsQuadratic ρ.dual A)
    (hbound : fixedCodim ρ.dual A ≤ 2 * rank D) :
    quadraticRatio (show Representation (ZMod 2) L J.toSubmodule from J.toRepresentation.comp L.subtype).dual ≤ 2 := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le hDA
  have hd : IsElementaryTwo (D.subgroupOf L) := ⟨by
    intro hz
    have hm := congrArg (Subgroup.map L.subtype) hz
    rw [map_subgroupOf_eq_of_le hDL,Subgroup.map_bot] at hm
    exact hD hm,IsElementaryAbelian.subgroupOf hDL⟩
  have hr : rank (D.subgroupOf L) = rank D := by
    rw [rank,rank,Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv]
  have h := dual_restriction_estimates ρ J L A D hDA hDL hquad
  exact (quadraticRatio_le_two_iff _).mpr ⟨D.subgroupOf L,hd,h.1,by rw [hr]; exact h.2.trans hbound⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
