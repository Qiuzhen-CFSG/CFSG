module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RadicalImages
public import Theory.SpecificGroups.SymplecticFour.RadicalParabolics.Exact

/-!
# The exact symplectic radical normalizer in C.2.7

Transport the literal intersection R*∩K* through the symplectic marking.
Its proved radical equation identifies its full normalizer, after a concrete
symplectic conjugacy, with a point parabolic, plane parabolic or Borel.
The statement keeps the original star quotient and requires no normalizer
placement. Placement in the original M_K* is the separate 8.9/10.5 step.

Source: Aschbacher (1981), 8.2(7); Aschbacher–Smith C.2.7, pp.146–147.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem star_symplectic_normalizer_parabolic_or_borel
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage K R K ≃* Sp F)
    (hne : (starImage K R R).subgroupOf (starImage K R K) ≠ ⊥) :
    ∃ g : Sp F,
      (normalizer ((starImage K R R).subgroupOf (starImage K R K) :
        Set (starImage K R K))).map
          ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = pointParabolic ∨
      (normalizer ((starImage K R R).subgroupOf (starImage K R K) :
        Set (starImage K R K))).map
          ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = planeParabolic ∨
      (normalizer ((starImage K R R).subgroupOf (starImage K R K) :
        Set (starImage K R K))).map
          ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = borel := by
  have hr := (star_intersection_radical_of_normal_input h hne).map_equiv e
  obtain ⟨g,hg⟩ := radical_normalizer_eq_parabolic_or_borel _ hr
  refine ⟨g,?_⟩
  rwa [←map_equiv_normalizer_eq,Subgroup.map_map] at hg
end CFSG.Quasithin.ChapterC.C27Source
