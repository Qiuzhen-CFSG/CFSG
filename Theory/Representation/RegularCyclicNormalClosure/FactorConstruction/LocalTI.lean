module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.MaximalIntersection
public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.InvolutionRank
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Transport

/-!
# Local TI geometry and ambient involutions

Under the maximal-intersection condition, distinct fixed-space images in
the pointwise fixer's orbit meet exactly in F. Thus their quotient images
are TI. Every involution in the fixer stabilizes every orbit member:
otherwise the ambient intersection rank bound contradicts the input.
The pair-intersection dimension is positive in U/F and at most dim S.

This is the local geometry for the maximal-intersection approach to
Aschbacher–Smith E.6.24, printed p.255, preparing GLS C.14.2 without imposing
its TI hypothesis on the original ambient action.
-/

public section

open Module Subgroup Representation.BinaryOffender
open Representation.GoldschmidtONan (orbit_map_mul orbit_map_one)
namespace Representation.RegularCyclicNormalClosure
namespace FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W}

/-- The actual fixer preserves the fixed subspace pointwise and setwise. -/
theorem pointwiseFixer_map (F : Submodule (ZMod 2) W) (g : pointwiseFixer ρ F) :
    F.map (ρ (g : A)) = F := by
  have hg := (mem_pointwiseFixer ρ F g).mp g.property
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    rwa [hg v hv]
  · intro v hv
    exact ⟨v, hv, hg v hv⟩

variable [FiniteDimensional (ZMod 2) W]

/-- A maximal intersection is the exact intersection of any two distinct
members of the orbit under its pointwise fixer. -/
theorem inf_eq_of_maximal (U F : Submodule (ZMod 2) W) (hFU : F ≤ U)
    (hmax : ∀ b : A, U.map (ρ b) ≠ U →
      finrank (ZMod 2) ↥(U ⊓ U.map (ρ b)) ≤ finrank (ZMod 2) F)
    (x y : pointwiseFixer ρ F) (hne : U.map (ρ (x : A)) ≠ U.map (ρ (y : A))) :
    U.map (ρ (x : A)) ⊓ U.map (ρ (y : A)) = F := by
  have hbase (b : pointwiseFixer ρ F) (hb : U.map (ρ (b : A)) ≠ U) :
      U ⊓ U.map (ρ (b : A)) = F := by
    have hle : F ≤ U ⊓ U.map (ρ (b : A)) :=
      le_inf hFU ((pointwiseFixer_map F b).ge.trans (Submodule.map_mono hFU))
    exact (Submodule.eq_of_le_of_finrank_eq hle
      (le_antisymm (Submodule.finrank_mono hle) (hmax b hb))).symm
  have he : U.map (ρ ((x⁻¹ * y : pointwiseFixer ρ F) : A)) ≠ U := by
    intro he
    apply hne
    have hh := congrArg (fun L : Submodule (ZMod 2) W => L.map (ρ (x : A))) he
    simpa only [← orbit_map_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      mul_inv_cancel_left] using hh.symm
  apply Submodule.map_injective_of_injective (ρ.apply_bijective (x : A)⁻¹).injective
  have hxF : F.map (ρ (x : A)⁻¹) = F := pointwiseFixer_map F (x⁻¹)
  rw [Submodule.map_inf _ (ρ.apply_bijective (x : A)⁻¹).injective,
    ← orbit_map_mul, inv_mul_cancel, orbit_map_one, ← orbit_map_mul,
    hxF]
  exact hbase (x⁻¹ * y) he

end FactorConstruction
open FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- The remaining dimension of the fixed space in a proper pair intersection
is positive and at most the original moved dimension. -/
theorem Input.intersection_dimensions (h : Input ρ C) (a : A)
    (hne : (fixedSpace ρ C).map (ρ a) ≠ fixedSpace ρ C) :
    finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)) <
        finrank (ZMod 2) (fixedSpace ρ C) ∧
      finrank (ZMod 2) (fixedSpace ρ C) ≤
        finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)) +
          finrank (ZMod 2) (displacementSpan ρ C ⊤) := by
  have he := (Submodule.equivMapOfInjective (ρ a) (ρ.apply_bijective a).injective
    (fixedSpace ρ C)).finrank_eq
  constructor
  · apply Submodule.finrank_lt_finrank_of_lt
    apply lt_of_le_of_ne inf_le_left
    intro heq
    have hle : fixedSpace ρ C ≤ (fixedSpace ρ C).map (ρ a) :=
      heq.ge.trans inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hle he).symm
  · have hb := h.le_fixed_inf_finrank a
    have hs := Submodule.finrank_add_eq_of_isCompl h.split
    omega

/-- Every ambient involution in the pointwise fixer stabilizes every member
of its fixed-space orbit. The rank estimate is on W, not on W/F. -/
theorem Input.involution_preserves_local_orbit (h : Input ρ C)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C)
    (hmax : ∀ b : A, (fixedSpace ρ C).map (ρ b) ≠ fixedSpace ρ C →
      finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ b)) ≤
        finrank (ZMod 2) F)
    (t x : pointwiseFixer ρ F) (ht : orderOf (t : A) = 2) :
    ((fixedSpace ρ C).map (ρ (x : A))).map (ρ (t : A)) =
      (fixedSpace ρ C).map (ρ (x : A)) := by
  by_contra hne
  have hi := inf_eq_of_maximal (ρ := ρ) (fixedSpace ρ C) F hFU hmax x (t * x)
    (by simpa only [Subgroup.coe_mul, orbit_map_mul] using Ne.symm hne)
  have hbound := fixedCodim_le_of_fixes_intersection ρ (t : A)
    (by simpa only [← ht] using pow_orderOf_eq_one (t : A))
    ((fixedSpace ρ C).map (ρ (x : A))) (by
      intro v hv
      apply (mem_pointwiseFixer ρ F t).mp t.property v
      rw [Subgroup.coe_mul, orbit_map_mul] at hi
      rwa [← hi])
  have he := (Submodule.equivMapOfInjective (ρ (x : A)) (ρ.apply_bijective (x : A)).injective
    (fixedSpace ρ C)).finrank_eq
  have hs := Submodule.finrank_add_eq_of_isCompl h.split
  have hn := h.no_small_involutions (t : A) ht
  omega

end Representation.RegularCyclicNormalClosure
