module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.CubicResidual
public import Stellmacher.SectionTwo.CubicSelectedQuotient
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The selected source module and the literal local normal closure

The local normal closure of the embedded Ω₁(Z(B)) lies between that
original seed and its ambient normal closure Z. The native selected factor
moves both bounds onto the same four-group, so it moves the literal localV
onto exactly that group. All maps are the original subgroup inclusions.
Elementary abelianness also descends from Z.

Source: Stellmacher (2.4), used in Aschbacher--Smith C.1.26, printed p.132.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Both containments use the original omega seed and inclusion. -/
theorem selected_localV_bounds (B K Z : Subgroup G) (hBK : B ≤ K)
    [Z.Normal] (hZ : omegaOneCenterAmbient B ≤ Z) :
    omegaOneCenterAmbient B ≤ (localV (inclusion hBK)).map K.subtype ∧
    (localV (inclusion hBK)).map K.subtype ≤ Z := by
  have he : ((omegaCenter B).map (inclusion hBK)).map K.subtype =
      omegaOneCenterAmbient B := by
    rw [map_map]
    rfl
  refine ⟨?_,?_⟩
  · rw [←he]
    exact map_mono le_normalClosure
  · apply map_le_iff_le_comap.mpr
    apply normalClosure_le_normal
    intro x hx
    exact hZ (he ▸ mem_map_of_mem K.subtype hx)

/-- The two original commutator bounds force the actual localV commutator. -/
theorem selected_localV_residual_map (B K Z : Subgroup G) (hBK : B ≤ K)
    [Z.Normal] (hZ : omegaOneCenterAmbient B ≤ Z)
    (hw : ⁅omegaOneCenterAmbient B,twoResidualAmbient K⁆ = ⁅Z,twoResidualAmbient K⁆) :
    (⁅localV (inclusion hBK),pResidual 2 K⁆ : Subgroup K).map K.subtype =
      ⁅Z,twoResidualAmbient K⁆ := by
  have hb := selected_localV_bounds B K Z hBK hZ
  rw [map_commutator, ←twoResidualSubgroup_eq_pResidual K]
  change ⁅(localV (inclusion hBK)).map K.subtype,twoResidualAmbient K⁆ = _
  exact le_antisymm (commutator_mono hb.2 le_rfl)
    (hw ▸ commutator_mono hb.1 le_rfl)

/-- The four points in the selected source module are exactly the four
points of the actual local residual commutator. -/
theorem selected_localV_residual_card (B K Z : Subgroup G) (hBK : B ≤ K)
    [Z.Normal] (hZ : omegaOneCenterAmbient B ≤ Z)
    (hw : ⁅omegaOneCenterAmbient B,twoResidualAmbient K⁆ = ⁅Z,twoResidualAmbient K⁆)
    (hc : Nat.card (⁅Z,twoResidualAmbient K⁆ : Subgroup G) = 4) :
    Nat.card (⁅localV (inclusion hBK),pResidual 2 K⁆ : Subgroup K) = 4 := by
  rw [←card_map_of_injective K.subtype_injective,
    selected_localV_residual_map B K Z hBK hZ hw,hc]

omit [Finite G] in
/-- Elementary abelianness is inherited from the original global normal closure. -/
theorem selected_localV_elementary (B K Z : Subgroup G) (hBK : B ≤ K)
    [Z.Normal] [IsElementaryAbelian 2 Z] (hZ : omegaOneCenterAmbient B ≤ Z) :
    IsElementaryAbelian 2 (localV (inclusion hBK)) := by
  have hle := (selected_localV_bounds B K Z hBK hZ).2
  let : IsElementaryAbelian 2 ((localV (inclusion hBK)).map K.subtype) :=
    IsElementaryAbelian.of_le hle
  have he : ((localV (inclusion hBK)).map K.subtype).subgroupOf K = localV (inclusion hBK) :=
    by
      change ((localV (inclusion hBK)).map K.subtype).comap K.subtype = _
      rw [comap_map_eq,ker_subtype,sup_bot_eq]
  exact he ▸ (IsElementaryAbelian.subgroupOf (map_subtype_le (localV (inclusion hBK))))

end CFSG.Quasithin.ChapterC.GlaubermanNiles
