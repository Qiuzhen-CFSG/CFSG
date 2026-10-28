module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Factorization of the literal source Cartan normalizer

The subgroup N_L(T_L), with T_L=T∩LO₂(LT), is T-invariant. Restricting
the ambient Sylow subgroup therefore gives its actual Sylow intersection.
The relative odd Hall condition defining the source Cartan X then gives
N_L(T_L)⊆TX as a set product. Every simultaneous normalizer of L and T
preserves this same subgroup, including its two-core contribution to T_L.

These elementary facts supply the Cartan part of the point-normalizer
calculation in Aschbacher--Smith 11.5.6(3), refs/quasithin.pdf,
printed pp.780--781, using the Cartan convention of Chapter 11.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions
open CFSG.Quasithin.Chapter12.Section02
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

include D in
omit [Finite G] in
/-- The source T_L=T∩LO₂(LT) is invariant under T. -/
theorem sylow_normalizes_sourceTL :
    (T : Subgroup G) ≤ normalizer (sourceTL T L : Set G) := by
  have hQ : (T : Subgroup G) ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    (le_sup_right.trans (L ⊔ (T : Subgroup G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact (le_inf (T : Subgroup G).le_normalizer
    ((le_inf D.sylow_normalizes_component hQ).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))).trans
        inf_normalizer_le_normalizer_inf

omit [Finite G] in
/-- Simultaneously normalizing L and T preserves the actual N_L(T_L). -/
theorem normalizes_cartanNormalizer {B : Subgroup G}
    (hBL : B ≤ normalizer (L : Set G))
    (hBT : B ≤ normalizer (T : Set G)) :
    B ≤ normalizer (cartanNormalizer T L : Set G) := by
  have hJ := (le_inf hBL hBT).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQ : B ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    hJ.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hTL : B ≤ normalizer (sourceTL T L : Set G) :=
    (le_inf hBT ((le_inf hBL hQ).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))).trans
        inf_normalizer_le_normalizer_inf
  exact (le_inf hBL (hTL.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

private theorem exists_sylow_intersection (J : Subgroup G)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G)) :
    ∃ P : Sylow 2 J, (P : Subgroup J) = (T : Subgroup G).subgroupOf J := by
  let W := J ⊔ (T : Subgroup G)
  have hJW : J ≤ W := le_sup_left
  let _ : (J.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJW).mpr (sup_le J.le_normalizer hTJ)
  obtain ⟨P, hP⟩ := (T.subtype (show (T : Subgroup G) ≤ W from le_sup_right)).exists_subgroupOf_eq_of_normal (J.subgroupOf W)
  let e := subgroupOfEquivOfLe hJW
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup _).map e.toMonoidHom = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, hJW x.property⟩, x.property⟩, hx, rfl⟩

include D in
/-- Every element of the source Cartan normalizer factors through T and X.
This uses the actual relative Hall condition, without assuming X normalizes T. -/
theorem cartanNormalizer_factorization {X : Subgroup G} (hX : IsCartan T L X)
    {g : G} (hg : g ∈ cartanNormalizer T L) :
    ∃ t ∈ (T : Subgroup G), ∃ x ∈ X, t * x = g := by
  have hTN : (T : Subgroup G) ≤ normalizer (cartanNormalizer T L : Set G) :=
    (le_inf D.sylow_normalizes_component
      ((sylow_normalizes_sourceTL D).trans (normalizer _).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  obtain ⟨P, hP⟩ := exists_sylow_intersection (cartanNormalizer T L) hTN
  have hcomp := OddHall.sylow_complement_of_hall P hX.2
  obtain ⟨⟨t, x⟩, he⟩ := hcomp.surjective (⟨g, hg⟩ : cartanNormalizer T L)
  have ht : t.val ∈ (T : Subgroup G).subgroupOf (cartanNormalizer T L) := by
    rw [← hP]
    exact t.property
  exact ⟨t.val.val, ht, x.val.val, x.property,
    congrArg Subtype.val he⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions
