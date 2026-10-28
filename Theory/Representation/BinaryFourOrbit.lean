module
public import Theory.LinearAlgebra.BinaryFourPointStabilizer
public import Theory.Representation.BinaryOffender.QuadraticImageBound

/-!
# A transitivity criterion in a binary four-space

A nonzero-vector stabilizer in GL₄(2) has order 1344. If a linear group
has order divisible by 45, orbit–stabilizer forces every nonzero orbit
size to be divisible by 15. There are exactly 15 nonzero vectors, so
the action is transitive. The representation application uses the literal
action image and lifts its elements to the original acting group.

Source application: Aschbacher–Smith E.2.15, printed p.228. This avoids
any representation recognition for the field-two symplectic equality case.
-/

public section
open Subgroup Module
namespace BinaryFourOrbit
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem transitive (hd : finrank (ZMod 2) W = 4)
    (H : Subgroup (W ≃ₗ[ZMod 2] W)) (hH : 45 ∣ Nat.card H)
    {v w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ a : H, (a : W ≃ₗ[ZMod 2] W) v = w := by
  classical
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Fintype W := Fintype.ofFinite W
  let : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun a : W ≃ₗ[ZMod 2] W => (a : W → W)) DFunLike.coe_injective
  let R := MulAction.stabilizer H v
  let j : R →* Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer v :=
    (H.subtype.comp R.subtype).codRestrict _ (fun a => a.property)
  have hj : Function.Injective j := by
    intro a b hab
    have hh := congrArg (fun z : Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer v =>
      (z : W ≃ₗ[ZMod 2] W)) hab
    exact Subtype.ext (Subtype.ext hh)
  have hr : Nat.card R ∣ 1344 := by
    have hh := card_dvd_of_injective j hj
    rwa [Theory.LinearAlgebra.BinaryFourPointStabilizer.card_stabilizer v hv hd] at hh
  let O := MulAction.orbit H v
  have hc : Nat.card O * Nat.card R = Nat.card H := by
    simpa only [R,MulAction.index_stabilizer,← Nat.card_coe_set_eq] using R.index_mul_card
  have h45 : 45 ∣ Nat.card O * 1344 := by
    rw [← hc] at hH
    exact hH.trans (Nat.mul_dvd_mul_left _ hr)
  have h15 : 15 ∣ Nat.card O := by
    have hh : 3*15 ∣ 3*(Nat.card O*448) := by convert h45 using 1; ring
    have hh' : 15 ∣ Nat.card O*448 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hh
    exact (show Nat.Coprime 15 448 by decide).dvd_of_dvd_mul_right hh'
  let f : O → {z : W // z ≠ 0} := fun z => ⟨z,by
    obtain ⟨a,ha⟩ := MulAction.mem_orbit_iff.mp z.property
    rw [← ha]
    intro hz
    exact hv ((a : W ≃ₗ[ZMod 2] W).injective (hz.trans (a : W ≃ₗ[ZMod 2] W).map_zero.symm))⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {z : W // z ≠ 0} => z.val) hab)
  have hn : Nat.card {z : W // z ≠ 0} = 15 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
      Fintype.card_unique (α := {z : W // z = 0}),
      Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card,hd]
    norm_num
  have ho : Nat.card O = 15 := by
    have hle := Nat.card_le_card_of_injective f hf
    rw [hn] at hle
    let : Nonempty O := ⟨⟨v,MulAction.mem_orbit_self v⟩⟩
    have hpos : 0 < Nat.card O := Nat.card_pos
    exact le_antisymm hle (Nat.le_of_dvd hpos h15)
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,by rw [ho,hn]⟩).2
  obtain ⟨z,hz⟩ := hs ⟨w,hw⟩
  have hz' : (z : W) = w := congrArg Subtype.val hz
  rw [← hz']
  exact MulAction.mem_orbit_iff.mp z.property

open Representation.BinaryOffender
variable {G : Type*} [Group G]
theorem representation_transitive
    (ρ : Representation (ZMod 2) G W) (hd : finrank (ZMod 2) W = 4)
    (hc : 45 ∣ Nat.card (actionImage ρ))
    {v w : W} (hv : v ≠ 0) (hw : w ≠ 0) : ∃ a : G, ρ a v = w := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W
  let f := e.toMonoidHom.comp ρ.asGroupHom
  have hH : 45 ∣ Nat.card f.range := by
    rw [MonoidHom.range_comp,card_map_of_injective e.injective]
    exact hc
  obtain ⟨a,ha⟩ := transitive hd f.range hH hv hw
  obtain ⟨g,hg⟩ := a.property
  refine ⟨g,?_⟩
  change f g v = w
  rw [hg]
  exact ha
end BinaryFourOrbit
