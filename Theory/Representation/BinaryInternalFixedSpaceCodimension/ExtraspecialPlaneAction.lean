module

public import Theory.Representation.BinaryInternalFixedSpaceCodimension.CentricSylowImage
public import Theory.GroupTheory.ExtraspecialSquare
public import Theory.GroupAction.Defs

/-!
# The literal extraspecial kernel acting on the opposite elementary plane

An extraspecial subgroup P of order128 intersects W in an elementary16.
Its action image therefore has order8 and exponent2. If the full centralizer
of P is its center, its fixed space on W is exactly the original central
line of P. This is the marked action needed after the Sylow-sixteen row
sieve in the original Held configuration.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Representation.BinaryInternalFixedSpaceCodimension
open BinaryOffender
variable {G : Type*} [Group G] [Finite G]

theorem extraspecial_plane_action
    (T : Sylow 2 G) (P W : Subgroup G)
    [IsExtraspecial 2 P] [IsElementaryAbelian 2 W]
    (hPT : P≤(T : Subgroup G)) (hWT : W≤(T : Subgroup G))
    (hTW : (T : Subgroup G)≤normalizer (W : Set G))
    (hPc : Nat.card P=128) (hI : Nat.card (P⊓W : Subgroup G)=16)
    (hZ : centerIn P≤W)
    (hCP : centralizer (P : Set G)=centerIn P)
    (hCW : centralizer (W : Set G)=W) :
    let I := normalizer (W : Set G)
    let ρ := representation W I le_rfl
    let τ := imageRepresentation ρ
    let A := actionSubgroup ρ (P.subgroupOf I)
    IsElementaryAbelian 2 A ∧ Nat.card A=8 ∧
      Module.finrank (ZMod 2) (fixedSpace τ A)=1 ∧
      ∀ v : Additive W, v∈fixedSpace τ A ↔ (v.toMul:G)∈centerIn P := by
  let I := normalizer (W : Set G)
  let ρ := representation W I le_rfl
  let τ := imageRepresentation ρ
  let q := actionHom ρ
  let A := actionSubgroup ρ (P.subgroupOf I)
  have hPI : P≤I := hPT.trans hTW
  have hker := (centric_sylow_image_card T W hWT hTW hCW).1
  have hAc : Nat.card A=8 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (P.subgroupOf I) q
    rw [hker] at hh
    change Nat.card ((P⊓W).subgroupOf I) * Nat.card A=Nat.card (P.subgroupOf I) at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hPI)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hPI).toEquiv,hI,hPc] at hh
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0<16) hh
  have hpow (x : A) : x^2=1 := by
    obtain ⟨p,hp,he⟩ := x.property
    apply Subtype.ext
    change (x : actionImage ρ)^2=1
    rw [←he,←map_pow]
    apply hker.ge
    apply hZ
    rw [centerIn_eq_map_center]
    exact ⟨(⟨p,hp⟩ : P)^2,IsExtraspecial.square_mem_center _,rfl⟩
  have hAe : IsElementaryAbelian 2 A := {
    toIsMulCommutative := ⟨⟨fun x y => Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hpow z)) x y⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  have hfix (v : Additive W) : v∈fixedSpace τ A ↔ (v.toMul:G)∈centerIn P := by
    rw [fixedSpace_actionSubgroup]
    exact (mem_invariants W I P le_rfl hPI v).trans (by rw [hCP])
  let e : fixedSpace τ A≃centerIn P := {
    toFun := fun v => ⟨v.val.toMul,(hfix v.val).mp v.property⟩
    invFun := fun z => ⟨Additive.ofMul ⟨z,hZ z.property⟩,(hfix _).mpr z.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hfc : Nat.card (fixedSpace τ A)=2 := by
    rw [Nat.card_congr e,centerIn_eq_map_center,card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 2 P
  have hdim : Module.finrank (ZMod 2) (fixedSpace τ A)=1 := by
    apply Nat.pow_right_injective (by decide : 1<2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace τ A)
    simpa only [hfc,Nat.card_zmod] using hh.symm
  exact ⟨hAe,hAc,hdim,hfix⟩

end Representation.BinaryInternalFixedSpaceCodimension
