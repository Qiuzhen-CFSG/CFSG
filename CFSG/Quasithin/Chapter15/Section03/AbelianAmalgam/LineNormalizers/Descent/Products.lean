module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.Frattini
public import Stellmacher.TwoResidualSylowSupplement
/-!
# Residual product and escape after descent

A Sylow subgroup of the original `G_E` restricts to a Sylow subgroup of
`C_G(E)`. Supplementing its two-residual gives `C_G(E) ≤ X_E T_E`.
Together with 15.3.66(6) and normalization, this proves the literal setwise
product `G_E = Y_E X_E T_E`. Consequently `X_E` escapes `M` whenever
`G_E` does and `Y,T ≤ M`.

These two conclusions do not need the common-residual collapse or the
terminal quotient recognition. Their inputs are the preceding geometric
product and the Sylow promotion, with no temporary replacement of `G_E`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemmas 15.3.66–67, printed pp.1152–1154, PDF pp.1169–1171.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
variable {G : Type*} [Group G] [Finite G]

/-- The original centralizer is covered by its two-residual and the line Sylow subgroup. -/
theorem centralizer_le_residual_sup_lineT (T E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    centralizer (E : Set G) ≤ lineX E ⊔ lineT T E := by
  let H := lineNormalizer E
  let C := (centralizer (E : Set G)).subgroupOf H
  let : C.Normal := inferInstance
  obtain ⟨P, hP⟩ := U.exists_sylow_map_eq_inf_of_normal C
  let f : C →* G := H.subtype.comp C.subtype
  have hC : C.map H.subtype = centralizer (E : Set G) :=
    map_subgroupOf_eq_of_le (centralizer_le_normalizer (E : Set G))
  have htop : (⊤ : Subgroup C).map f = centralizer (E : Set G) := by
    rw [← map_map, ← MonoidHom.range_eq_map, C.range_subtype, hC]
  have hres : (Stellmacher.twoResidualAmbient (⊤ : Subgroup C)).map f = lineX E :=
    map_twoResidualAmbient_of_subgroup_image ⊤ f _ htop
  have hPl : (P : Subgroup C).map f ≤ lineT T E := by
    rw [← map_map, hP, map_inf _ _ _ H.subtype_injective, hU]
    exact inf_le_left
  have hsup := congrArg (Subgroup.map f) (Stellmacher.twoResidualAmbient_top_sup_sylow P)
  rw [Subgroup.map_sup, hres, htop] at hsup
  rw [← hsup]
  exact sup_le_sup_left hPl _

/-- The setwise residual product in 15.3.67(3), for the original line normalizer. -/
theorem original_residual_product (Y T E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hTY : T ≤ normalizer (Y : Set G))
    (hgeom : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineT T E : Set G) * (centralizer (E : Set G) : Set G)) :
    (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineX E : Set G) * (lineT T E : Set G) := by
  have hYG : lineY Y E ≤ lineNormalizer E := (lineY_le Y E).trans inf_le_right
  have hXG : lineX E ≤ lineNormalizer E :=
    (lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G))
  have hYX : lineY Y E ≤ normalizer (lineX E : Set G) :=
    hYG.trans (lineNormalizer_le_normalizer_lineX E)
  have hTX : lineT T E ≤ normalizer (lineX E : Set G) :=
    inf_le_right.trans (lineNormalizer_le_normalizer_lineX E)
  have hTn : lineT T E ≤ normalizer ((lineY Y E ⊔ lineX E : Subgroup G) : Set G) :=
    (le_inf (lineT_le_normalizer_lineY Y T E hTY) hTX).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have heq : lineNormalizer E = (lineY Y E ⊔ lineX E) ⊔ lineT T E := by
    apply le_antisymm
    · intro g hg
      change g ∈ (lineNormalizer E : Set G) at hg
      rw [hgeom] at hg
      obtain ⟨yt, ⟨y, hy, t, ht, rfl⟩, c, hc, rfl⟩ := hg
      apply mul_mem
      · exact mul_mem (mem_sup_left (mem_sup_left hy)) (mem_sup_right ht)
      · have hle : lineX E ⊔ lineT T E ≤ (lineY Y E ⊔ lineX E) ⊔ lineT T E :=
          sup_le (le_sup_right.trans le_sup_left) le_sup_right
        exact hle (centralizer_le_residual_sup_lineT T E U hU hc)
    · exact sup_le (sup_le hYG hXG) inf_le_right
  rw [heq, coe_mul_of_right_le_normalizer_left _ _ hTn,
    coe_mul_of_left_le_normalizer_right _ _ hYX]

/-- The residual `X_E` must escape `M` because the remaining factors lie in `M`. -/
theorem lineX_not_le_of_escape (M Y T E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hTY : T ≤ normalizer (Y : Set G)) (hYM : Y ≤ M) (hTM : T ≤ M)
    (hout : ¬ lineNormalizer E ≤ M)
    (hgeom : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineT T E : Set G) * (centralizer (E : Set G) : Set G)) :
    ¬ lineX E ≤ M := by
  intro hXM
  apply hout
  intro g hg
  change g ∈ (lineNormalizer E : Set G) at hg
  rw [original_residual_product Y T E U hU hTY hgeom] at hg
  obtain ⟨yx, ⟨y, hy, x, hx, rfl⟩, t, ht, rfl⟩ := hg
  exact M.mul_mem (M.mul_mem (hYM (lineY_le Y E hy).1) (hXM hx)) (hTM ht.1)
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
