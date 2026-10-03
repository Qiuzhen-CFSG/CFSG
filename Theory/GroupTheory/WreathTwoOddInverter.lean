module

public import Theory.GroupTheory.WreathTwoSylowCentralizer
public import Theory.PPrimeCore
public import Stellmacher.LaterDefs
public import Stellmacher.SectionOne.Defs

/-!
# An odd-core inverter in a wreath Sylow actor

In a finite group isomorphic to `SL₂(2) ≀ᵣ C₂`, every normal elementary
four-subgroup of a Sylow two-subgroup contains an involution inverting the
whole odd core. The odd core has order nine.

The concrete subgroup consists of base elements whose two coordinates have
cube one. Closure is checked in the six-element `SL₂(2)` factor; normality
follows by conjugating powers. Its coordinate equivalence gives order nine.
It is contained in the odd core, and the odd core's order is coprime to two
and divides 72, so equality follows. The central rotation of the exposed
dihedral Sylow model has a transvection in both coordinates and inverts this
subgroup. The existing Sylow centralizer containment puts that rotation in
every actor of order at least four. Thus normality and elementary structure
are not needed for the internal membership argument, although the public
theorem retains the requested actor hypotheses.

Actual ambient Sylow conjugacy and the supplied group isomorphism transport
both the actor and the odd core. No representation hypotheses are used.
This supplies the wreath-group calculation for the chief-factor argument
on journal p.47 (PDF p.37) of Stellmacher's paper. No Section Nine results
are imported. All finite certificates use kernel reduction.
-/

open Stellmacher.SectionOne

namespace Theory.GroupTheory

private abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev W := RegularWreathProduct SL2 C2
private instance : DecidableEq W := fun first second => decidable_of_iff
  (first.left = second.left ∧ first.right = second.right) RegularWreathProduct.ext_iff.symm

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 100000

private theorem sl2_cube_mul : ∀ first second : SL2,
    first ^ 3 = 1 → second ^ 3 = 1 → (first * second) ^ 3 = 1 := by
  decide +kernel


private def cubeSubgroup : Subgroup W where
  carrier := {element | element.right = 1 ∧ ∀ coordinate, (element.left coordinate) ^ 3 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro first second hfirst hsecond
    exact ⟨by simp [hfirst.1, hsecond.1], fun coordinate =>
      sl2_cube_mul _ _ (hfirst.2 coordinate) (hsecond.2 _)⟩
  inv_mem' := by
    intro element helement
    refine ⟨by simp [helement.1], ?_⟩
    intro coordinate
    simpa only [RegularWreathProduct.inv_left, Pi.inv_apply, inv_pow, inv_one]
      using congrArg Inv.inv (helement.2 (element.right * coordinate))

private instance : cubeSubgroup.Normal where
  conj_mem element helement conjugator := by
    obtain ⟨hright, hleft⟩ := helement
    refine ⟨by simp [hright], ?_⟩
    intro coordinate
    have hcoordinate : (conjugator * element * conjugator⁻¹).left coordinate =
        conjugator.left coordinate * element.left (conjugator.right⁻¹ * coordinate) *
          (conjugator.left coordinate)⁻¹ := by
      simp [hright]
    rw [hcoordinate, conj_pow, hleft]
    simp

private theorem cube_card : Nat.card cubeSubgroup = 9 := by
  let coordinates : cubeSubgroup ≃ (C2 → {element : SL2 // element ^ 3 = 1}) := {
    toFun := fun element coordinate => ⟨element.val.left coordinate, element.property.2 coordinate⟩
    invFun := fun values => ⟨⟨fun coordinate => (values coordinate).val, 1⟩,
      rfl, fun coordinate => (values coordinate).property⟩
    left_inv := fun element => by
      apply Subtype.ext
      exact RegularWreathProduct.ext rfl element.property.1.symm
    right_inv := fun values => rfl }
  rw [Nat.card_congr coordinates, Nat.card_fun]
  have hcard : Nat.card {element : SL2 // element ^ 3 = 1} = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hcard]
  norm_num [Nat.card_eq_fintype_card]

private theorem wreath_card : Nat.card W = 72 := by
  rw [RegularWreathProduct.card]
  have hcard : Nat.card SL2 = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hcard]
  norm_num [Nat.card_eq_fintype_card]


private theorem cube_eq_oddCore : cubeSubgroup = oddCore W := by
  have hle : cubeSubgroup ≤ oddCore W := by
    apply le_sSup
    exact ⟨inferInstance, by rw [cube_card]; decide⟩
  have hcop := pPrimeCore_coprime_card (p := 2) (G := W)
  have hdiv := (oddCore W).card_subgroup_dvd_card
  rw [wreath_card] at hdiv
  have hcop8 : Nat.Coprime (Nat.card (oddCore W)) 8 := by
    exact hcop.symm.pow_right 3
  have hdiv9 : Nat.card (oddCore W) ∣ 9 := hcop8.dvd_of_dvd_mul_left hdiv
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [cube_card]; exact Nat.le_of_dvd (by decide) hdiv9)

private theorem standard_inverter :
    IsInvolution (wreathTwoDihedralHom (DihedralGroup.r 2)) ∧
    ∀ element : W, element ∈ cubeSubgroup →
      wreathTwoDihedralHom (DihedralGroup.r 2) * element *
        (wreathTwoDihedralHom (DihedralGroup.r 2))⁻¹ = element⁻¹ := by
  let transvection : SL2 := ⟨!![1, 1; 0, 1], by decide⟩
  have hinvert : ∀ element : SL2, element ^ 3 = 1 →
      transvection * element * transvection⁻¹ = element⁻¹ := by decide +kernel
  have hcoordinates : wreathTwoDihedralHom (DihedralGroup.r 2) =
      (⟨fun _ => transvection, 1⟩ : W) := by decide +kernel
  constructor
  · unfold IsInvolution
    decide +kernel
  · intro element helement
    obtain ⟨hright, hleft⟩ := helement
    rw [hcoordinates]
    apply RegularWreathProduct.ext
    · funext coordinate
      simpa [hright] using hinvert (element.left coordinate) (hleft coordinate)
    · simp [hright]


private theorem standard_actor_inverter (actor : Subgroup W)
    (actor_le : actor ≤ (wreathTwoSylow : Subgroup W))
    (actor_card : 4 ≤ Nat.card actor) :
    ∃ element : W, element ∈ actor ∧ IsInvolution element ∧
      ∀ odd : oddCore W, element * (odd : W) * element⁻¹ = (odd : W)⁻¹ := by
  let element := wreathTwoDihedralHom (DihedralGroup.r 2)
  have hcentral : ∀ other : DihedralGroup 4,
      other * DihedralGroup.r 2 = DihedralGroup.r 2 * other := by decide +kernel
  have hmem : element ∈ (wreathTwoSylow : Subgroup W) := by
    rw [wreathTwoSylow_coe]
    exact ⟨DihedralGroup.r 2, rfl⟩
  have hcent : element ∈ Subgroup.centralizer (actor : Set W) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    obtain ⟨preimage, rfl⟩ := (wreathTwoSylow_coe ▸ actor_le hother)
    exact (map_mul wreathTwoDihedralHom preimage (DihedralGroup.r 2)).symm.trans
      ((congrArg wreathTwoDihedralHom (hcentral preimage)).trans
        (map_mul wreathTwoDihedralHom (DihedralGroup.r 2) preimage))
  refine ⟨element, (wreath_two_sylow_centralizer_le_of_card_ge_four
    wreathTwoSylow actor actor_le actor_card).1 ⟨hmem, hcent⟩,
    standard_inverter.1, ?_⟩
  intro odd
  have hodd : (odd : W) ∈ cubeSubgroup := cube_eq_oddCore.symm ▸ odd.property
  exact standard_inverter.2 odd hodd

/-- A normal elementary four in a wreath Sylow contains a full odd-core
inverter, and that odd core has order nine. -/
public theorem wreathTwo_exists_actor_oddCore_inverter
    {X : Type*} [Group X] [Finite X]
    (model : Nonempty (X ≃* Stellmacher.Later.SL2TwoWreathC2))
    (sylow : Sylow 2 X) (actor : Subgroup X)
    (actor_le : actor ≤ (sylow : Subgroup X))
    (_actor_normal : (actor.subgroupOf (sylow : Subgroup X)).Normal)
    (_actor_elementary : IsElementaryAbelian 2 actor)
    (actor_card : Nat.card actor = 4) :
    Nat.card (oddCore X) = 9 ∧ ∃ element : X,
      element ∈ actor ∧ IsInvolution element ∧
        ∀ odd : oddCore X, element * (odd : X) * element⁻¹ = (odd : X)⁻¹ := by
  obtain ⟨modelEquiv⟩ := model
  let imageSylow := sylow.mapSurjective (f := modelEquiv.toMonoidHom) modelEquiv.surjective
  obtain ⟨conjugator, hconjugator⟩ :=
    MulAction.exists_smul_eq W wreathTwoSylow imageSylow
  let conjugation := MulAut.conj conjugator
  let equiv := modelEquiv.trans conjugation.symm
  have hsylow : (sylow : Subgroup X).map equiv.toMonoidHom =
      (wreathTwoSylow : Subgroup W) := by
    rw [show equiv.toMonoidHom = conjugation.symm.toMonoidHom.comp
      modelEquiv.toMonoidHom from rfl, ← Subgroup.map_map]
    apply (Subgroup.map_symm_eq_iff_map_eq (e := conjugation)
      (wreathTwoSylow : Subgroup W)).mpr
    exact congrArg (fun subgroup : Sylow 2 W => (subgroup : Subgroup W)) hconjugator
  let imageActor := actor.map equiv.toMonoidHom
  have himage_le : imageActor ≤ (wreathTwoSylow : Subgroup W) := by
    rw [← hsylow]
    exact Subgroup.map_mono actor_le
  have himage_card : 4 ≤ Nat.card imageActor := by
    change 4 ≤ Nat.card (actor.map (equiv : X →* W))
    rw [← Nat.card_congr (equiv.subgroupMap actor).toEquiv, actor_card]
  have hcore : (oddCore X).map equiv.toMonoidHom = oddCore W :=
    pPrimeCore_map_iso 2 equiv
  have hcore_card : Nat.card (oddCore X) = 9 := by
    calc
      Nat.card (oddCore X) = Nat.card ((oddCore X).map equiv.toMonoidHom) :=
        Nat.card_congr (equiv.subgroupMap (oddCore X)).toEquiv
      _ = 9 := by rw [hcore, ← cube_eq_oddCore, cube_card]
  obtain ⟨element, helement, hinvolution, hinvert⟩ :=
    standard_actor_inverter imageActor himage_le himage_card
  refine ⟨hcore_card, equiv.symm element, ?_, ?_, ?_⟩
  · obtain ⟨preimage, hpreimage, rfl⟩ := helement
    simpa using hpreimage
  · constructor
    · intro hone
      apply hinvolution.1
      simpa using congrArg equiv hone
    · apply equiv.injective
      simpa only [map_pow, equiv.apply_symm_apply, map_one] using hinvolution.2
  · intro odd
    have hodd : equiv odd ∈ oddCore W := hcore ▸
      (show equiv odd ∈ (oddCore X).map equiv.toMonoidHom from ⟨odd, odd.property, rfl⟩)
    apply equiv.injective
    simpa only [map_mul, map_inv, equiv.apply_symm_apply] using
      hinvert ⟨equiv odd, hodd⟩


end Theory.GroupTheory
