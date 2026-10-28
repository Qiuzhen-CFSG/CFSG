module
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FourEndpointResidual
public import Theory.Representation.BinaryTransvectionGroups.Basic
/-!
# Exact order and exponent bound of the degree-four endpoint residual

The endpoint parabolic has order 576 and its two-core quotient is S₃ × S₃.
The two-core therefore has order sixteen. The residual image has order nine,
so its kernel has at most sixteen elements. The checked sixteen root
rectangles give the reverse bound, proving |O²(P)| = 144 exactly.
Every residual element cubes into the elementary two-core, so its sixth
power is one.

This is the model boundary for the ordinary graph-action application of
Aschbacher--Smith 15.1.22(7), printed pp.1099--1100. It does not imply the
strict lower bound available for characteristic-two covering components.
-/
public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic SmallParabolicLevi
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

/-- The endpoint residual has exactly 144 elements. -/
theorem four_endpoint_residual_card (b : Basis 3) :
    Nat.card (pResidual 2 (parabolic (cutSpace b 1))) = 144 := by
  let W := cutSpace b (1 : Fin 3)
  let E := parabolic W
  let R := pResidual 2 E
  let q := QuotientGroup.mk' (pCore 2 E)
  let f := q.subgroupMap R
  have hW : Module.finrank (ZMod 2) W = 2 := cutSpace_finrank b 1
  have hQ : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 2 := by
    have hh := W.finrank_quotient_add_finrank
    rw [hW] at hh
    simp [Space] at hh
    omega
  let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hW)
  let c : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hQ)
  let e := (quotientTwoCoreEquivOfCoordinates W a c).trans
    (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree)
  have him : Nat.card (R.map q) = 9 := by
    rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
    have hh := congrArg (fun D : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) => Nat.card D)
      (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective)
    rw [card_map_of_injective e.injective,SymmetricThreeProductResidual.residual_card] at hh
    exact hh
  have hcore : Nat.card (pCore 2 E) = 16 := by
    have hc := (pCore 2 E).card_mul_index
    have hquot : (pCore 2 E).index = 36 := by
      change Nat.card (E ⧸ pCore 2 E) = 36
      rw [Nat.card_congr e.toEquiv,Nat.card_prod]
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    rw [hquot,(four_endpoint_residual_data b).1] at hc
    omega
  have hk : Nat.card f.ker ≤ 16 := by
    let g : f.ker → pCore 2 E := fun x => ⟨((x : R) : E), by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val x.property⟩
    have hg : Function.Injective g := by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : pCore 2 E => (z : E)) he
    simpa only [hcore] using Nat.card_le_card_of_injective g hg
  have hc := f.ker.card_mul_index
  rw [index_ker,f.range_eq_top_of_surjective (q.subgroupMap_surjective R),card_top,him] at hc
  have hlo := (four_endpoint_residual_data b).2
  change 144 ≤ Nat.card R at hlo
  change Nat.card R = 144
  omega

/-- Every sixth power in the actual degree-four endpoint residual is one. -/
theorem four_endpoint_residual_pow_six (b : Basis 3)
    (x : parabolic (cutSpace b 1)) (hx : x ∈ pResidual 2 (parabolic (cutSpace b 1))) :
    x ^ 6 = 1 := by
  let W := cutSpace b (1 : Fin 3)
  let E := parabolic W
  have hW : Module.finrank (ZMod 2) W = 2 := cutSpace_finrank b 1
  have hQ : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 2 := by
    have hh := W.finrank_quotient_add_finrank
    rw [hW] at hh
    simp [Space] at hh
    omega
  let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hW)
  let c : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hQ)
  let e := (quotientTwoCoreEquivOfCoordinates W a c).trans
    (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 E))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hy : q x ∈ pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
    rw [←map_pResidual_of_surjective 2 q hq]
    exact mem_map_of_mem q hx
  rw [SymmetricThreeProductResidual.residual_eq] at hy
  have hpow (y : Equiv.Perm (Fin 3)) (hy : y ∈ alternatingGroup (Fin 3)) : y^3=1 := by
    have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup,Nat.card_fin]
      rfl
    have hh := pow_card_eq_one' (x := (⟨y,hy⟩ : alternatingGroup (Fin 3)))
    rw [hc] at hh
    exact congrArg Subtype.val hh
  have hy3 : (q x)^3=1 := Prod.ext (hpow _ hy.1) (hpow _ hy.2)
  have hx3 : x^3 ∈ pCore 2 E := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    change q (x^3) = e 1
    rw [map_pow,map_one,hy3]
  let f : pCore 2 E →* LinearGroup 4 := E.subtype.comp (pCore 2 E).subtype
  let : IsElementaryAbelian 2 (pCore 2 E) :=
    BinaryTransvectionGroups.elementaryAbelian_of_le_radical f
      (E.subtype_injective.comp (pCore 2 E).subtype_injective) W (by
        intro z
        exact (show pCore 2 E ≤ (radical W).subgroupOf E from
          (twoCore_eq_radical W).le) z.property)
  have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) (x^3) hx3
  simpa only [←pow_mul] using hh

end BinaryLinear.InvariantNodeActions
