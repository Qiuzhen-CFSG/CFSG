module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicSeed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.Thompson

/-!
# Cubic containment on the actual H-star intersection

If a cubic in H ∩ N_G(L) escaped L, the checked Thompson argument would
force that intersection to normalize the original seed. The seed stabilizer
calculation then puts the same cubic in L, a contradiction. This proves the
restricted SL₃ statement needed for 11.3.7. The other marked rows follow
from their checked prime-to-three residual equalities.

This does not assert unrestricted 11.0.4. The final chosen-natural assembly
remains with qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, 11.0.3--4 and 11.3.7, printed pp.760,773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- An exact ambient prime-to-three residual equality contains every cubic. -/
private theorem orderThree_mem_of_cubic_residual {M L : Subgroup G}
    (hres : L = (primeToResidual 3 M).map M.subtype)
    {x : G} (hxM : x ∈ M) (hx3 : orderOf x = 3) : x ∈ L := by
  have hxpow : (⟨x,hxM⟩ : M) ^ (3 ^ 1) = 1 := by
    apply Subtype.ext
    simpa only [coe_pow,coe_one,pow_one,hx3] using pow_orderOf_eq_one x
  rw [hres]
  exact mem_map_of_mem M.subtype (mem_primeToResidual_of_pow hxpow)

variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Every cubic in the original Sp₄ normalizer lies in the component. -/
theorem sp4_orderThree_mem
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx3 : orderOf x = 3) : x ∈ L :=
  orderThree_mem_of_cubic_residual (sp4_cubic_residual D S m) hxM hx3

/-- Every cubic in the original G₂ normalizer lies in the component. -/
theorem g2_orderThree_mem
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx3 : orderOf x = 3) : x ∈ L :=
  orderThree_mem_of_cubic_residual (g2_cubic_residual D S m) hxM hx3

/-- The even-degree SL₃ cubic clause restricted to the actual H-star intersection. -/
theorem sl3_orderThree_mem_of_hStar
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {x : G} (hxH : x ∈ H) (hxM : x ∈ normalizer (L : Set G))
    (hx3 : orderOf x = 3) : x ∈ L := by
  by_contra hxL
  have hxV := (sl3_intersection_normalizes_of_cubic_outside D S m heven
    hxM hx3 hxL H hH ⟨hxH,hxM⟩).2
  exact hxL (sl3_orderThree_mem_of_normalizes_seed D S m heven hxM hxV hx3)

/-- The restricted cubic clause uses the actual marked action in every row. -/
theorem natural_orderThree_mem_of_hStar (c : Coordinates D S.field)
    (heven : Even S.field.degree) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {x : G} (hxH : x ∈ H) (hxM : x ∈ normalizer (L : Set G))
    (hx3 : orderOf x = 3) : x ∈ L := by
  cases c with
  | sl3 m => exact sl3_orderThree_mem_of_hStar D S m heven hH hxH hxM hx3
  | sp4 m => exact sp4_orderThree_mem D S m hxM hx3
  | g2 m => exact g2_orderThree_mem D S m hxM hx3

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
