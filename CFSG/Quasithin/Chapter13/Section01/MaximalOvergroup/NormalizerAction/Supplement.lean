module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.NormalizerAction.Source
public import Theory.GroupTheory.SolvableRadical.Supplement

/-!
# The original radical supplements have the same action image

A radical supplement B≤L has the full L-image in the actual normalizer
quotient. Its kernel is its own solvable radical, by solvable-kernel
transport. The first isomorphism theorem therefore identifies
B/O∞(B) with that same literal component image, compatibly with inclusion.

Source: Aschbacher--Smith 13.1.8 and the first paragraph of13.1.9,
printed pp.868--869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.NormalizerReducedAction
variable {G : Type*} [Group G] [Finite G] {L B : Subgroup G}

omit [Finite G] in
private theorem internal_supplement (hBL : B ≤ L)
    (hgen : (solvableRadical L).map L.subtype ⊔ B = L) :
    solvableRadical L ⊔ (inclusion hBL).range = ⊤ := by
  apply map_injective L.subtype_injective
  rw [Subgroup.map_sup, ← MonoidHom.range_comp, ← MonoidHom.range_eq_map,range_subtype]
  change (solvableRadical L).map L.subtype ⊔ B.subtype.range = L
  simpa only [range_subtype] using hgen

theorem supplement_kernel (hBL : B ≤ L)
    (hk : (componentMap L).ker = solvableRadical L)
    (hgen : (solvableRadical L).map L.subtype ⊔ B = L) :
    ((componentMap L).comp (inclusion hBL)).ker = solvableRadical B := by
  rw [← MonoidHom.comap_ker,hk]
  exact solvableRadical_comap_of_injective_supplement (inclusion hBL)
    (inclusion_injective hBL) (internal_supplement hBL hgen)

omit [Finite G] in
theorem supplement_range (hBL : B ≤ L)
    (hk : (componentMap L).ker = solvableRadical L)
    (hgen : (solvableRadical L).map L.subtype ⊔ B = L) :
    ((componentMap L).comp (inclusion hBL)).range = componentImage L := by
  have he := congrArg (Subgroup.map (componentMap L)) (internal_supplement hBL hgen)
  have hzero : (solvableRadical L).map (componentMap L) = ⊥ := by
    rw [← hk]
    exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
  rw [Subgroup.map_sup,hzero,bot_sup_eq,← MonoidHom.range_eq_map] at he
  rw [MonoidHom.range_comp,he,componentMap_range]

noncomputable def supplementQuotientEquiv (hBL : B ≤ L)
    (hk : (componentMap L).ker = solvableRadical L)
    (hgen : (solvableRadical L).map L.subtype ⊔ B = L) :
    (B ⧸ solvableRadical B) ≃* componentImage L :=
  (QuotientGroup.quotientMulEquivOfEq (supplement_kernel hBL hk hgen).symm).trans
    ((QuotientGroup.quotientKerEquivRange ((componentMap L).comp (inclusion hBL))).trans
      (MulEquiv.subgroupCongr (supplement_range hBL hk hgen)))

theorem supplementQuotientEquiv_mk (hBL : B ≤ L)
    (hk : (componentMap L).ker = solvableRadical L)
    (hgen : (solvableRadical L).map L.subtype ⊔ B = L) (b : B) :
    (supplementQuotientEquiv hBL hk hgen (QuotientGroup.mk' (solvableRadical B) b) : Star L) =
      componentMap L (inclusion hBL b) := by
  simp only [supplementQuotientEquiv,MulEquiv.trans_apply]
  rfl

end CFSG.Quasithin.Chapter13.Section01.NormalizerReducedAction
