module
public import Theory.SpecificGroups.SymmetricSix.TranspositionCubic.Movement
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# Cubic movement on the six-letter augmentation core

Every lift of a transposition-fixed natural vector is fixed in the original
five-dimensional core, because a transposition has an unchanged coordinate.
Cubic movement therefore lifts through the actual core-to-natural quotient.
The coordinate marking transports this movement into the literal normal
closure of the omega-center, without selecting a four-dimensional subgroup.

Source: Aschbacher–Smith C.1.24(c), pp.130–131, and its application in
13.2.2(7), pp.877–878. The Chapter C core extension consumes this calculation.
-/

public section
open Subgroup Representation.BinaryOffender BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.TranspositionCubic

/-- A transposition-fixed vector of the natural quotient has every lift
fixed in the augmentation core: a transposition has a fixed coordinate,
so a constant displacement must be zero. -/
theorem core_fixed_of_natural_fixed (r : Sym) (hr : r.IsSwap)
    (v : core (Fin 6))
    (hv : naturalRepresentation (Fin 6) r (coreToNatural (Fin 6) v) =
      coreToNatural (Fin 6) v) : coreRepresentation (Fin 6) r v = v := by
  obtain ⟨i,j,hij,rfl⟩ := hr
  obtain ⟨k,hki,hkj⟩ := (by decide : ∀ i j : Fin 6, ∃ k : Fin 6, k ≠ i ∧ k ≠ j) i j
  have hh := congrArg Subtype.val hv
  change deletedRepresentation (Fin 6) (Equiv.swap i j) ((constants (Fin 6)).mkQ v.val) =
    (constants (Fin 6)).mkQ v.val at hh
  apply Subtype.ext
  exact (swap_fixed_iff i j v.val).mpr ((deleted_swap_fixed_iff i j k hki hkj v.val).mp hh)

/-- Cubic movement of a transposition-fixed natural vector lifts to the
original five-space without choosing a natural submodule. -/
theorem core_fixed_movement_of_natural (r c : Sym) (hr : r.IsSwap)
    (hm : ¬fixedSpace (naturalRepresentation (Fin 6)) (zpowers r) ≤
      fixedSpace (naturalRepresentation (Fin 6)) (zpowers c)) :
    ¬fixedSpace (coreRepresentation (Fin 6)) (zpowers r) ≤
      fixedSpace (coreRepresentation (Fin 6)) (zpowers c) := by
  intro h
  apply hm
  intro w hw
  obtain ⟨v,rfl⟩ := coreToNatural_surjective w
  have hv := core_fixed_of_natural_fixed r hr v ((mem_fixedSpace_zpowers_iff _ _ _).mp hw)
  have hc := (mem_fixedSpace_zpowers_iff _ _ _).mp
    (h ((mem_fixedSpace_zpowers_iff _ _ _).mpr hv))
  apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
  rw [←coreToNatural_equivariant,hc]

open Stellmacher Representation.BinaryOffender
variable {G : Type*} [Group G]
theorem core_omega_span_moved (V R A : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (q : G →* Sym)
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q g) (e v).toAdd)
    (r c : Sym) (hR : R.map q ≤ zpowers r) (hrA : r ∈ A.map q) (hcG : c ∈ q.range)
    (hc : c^3=1) (hi : r*c*r⁻¹=c⁻¹)
    (hm : ¬fixedSpace (BinaryPermutation.coreRepresentation (Fin 6)) (zpowers r) ≤
      fixedSpace (BinaryPermutation.coreRepresentation (Fin 6)) (zpowers c)) :
    ¬ A ≤ centralizer (normalClosure (omegaOneCenterAmbient R : Set G) : Set G) := by
  obtain ⟨v,hv,hcv⟩ := exists_moved_cubic_translate _ r c hc hi hm
  let u : V := e.symm (Multiplicative.ofAdd v)
  have heu : (e u).toAdd=v := congrArg Multiplicative.toAdd (e.apply_symm_apply _)
  have huv : v ∈ fixedSpace (BinaryPermutation.coreRepresentation (Fin 6)) (zpowers r) :=
    (mem_fixedSpace_zpowers_iff _ _ _).mpr hv
  have huR : (u:G) ∈ omegaOneCenterAmbient R := by
    apply (mem_omegaOneCenterAmbient_iff R (u:G)).mpr
    refine ⟨hVR u.property,elemPow_eq_one_of_isElementaryAbelian (u:G) u.property,?_⟩
    intro a ha
    have hfix : MulAut.conjNormal a u=u := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [he,heu]
      exact huv ⟨q a,hR (mem_map_of_mem q ha)⟩
    have hh := congrArg (fun z : V => (z:G)) hfix
    change a*(u:G)*a⁻¹=(u:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨g,hg⟩ := hcG
  let w : V := MulAut.conjNormal g u
  have hw : (w:G) ∈ normalClosure (omegaOneCenterAmbient R : Set G) :=
    (normalClosure_normal.conj_mem _ (subset_normalClosure huR) g)
  obtain ⟨a,ha,hqa⟩ := hrA
  intro hA
  have hfix : MulAut.conjNormal a w=w := by
    apply Subtype.ext
    change a*(w:G)*a⁻¹=(w:G)
    rw [←hA ha (w:G) hw]
    group
  have hh := he a w
  rw [hfix,hqa] at hh
  have hwcoord : (e w).toAdd=BinaryPermutation.coreRepresentation (Fin 6) c v := by
    rw [show w=MulAut.conjNormal g u from rfl,he,hg,heu]
  rw [hwcoord] at hh
  exact hcv hh.symm
end Theory.SpecificGroups.SymmetricSix.TranspositionCubic
