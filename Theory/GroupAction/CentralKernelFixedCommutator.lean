module
public import Theory.GroupAction.PPerfectFixedLifting
public import Mathlib.GroupTheory.Sylow
/-!
# Derived fixed groups through central kernels

Central displacement is an abelian-valued homomorphism. It vanishes on
the derived subgroup of a quotient-fixed preimage, so the image of the
fixed group contains the derived group of the quotient fixed group.
The Sylow consequence compares this derived subgroup with a second fixed
group containing the image of the supplied Sylow subgroup. No coprimeness
or fixed-point lifting assumption is used.

This is the central-cover comparison needed for Aschbacher–Smith E.6.23,
printed p.254 (PDF p.265), in the Higman–Sims case.
-/

public section
namespace MulAut
open Subgroup
variable {G H : Type*} [Group G] [Group H]

theorem fixes_commutator_of_central_displacement
    (a : MulAut G) (f : G →* H) (hc : f.ker ≤ center G)
    (X : Subgroup G) (hX : ∀ x ∈ X, f (a x) = f x) :
    (commutator X).map X.subtype ≤ a.fixedSubgroup := by
  have hdmem (x : X) : a x * (x : G)⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hX x x.property, mul_inv_cancel]
  let d : X →* center G := {
    toFun x := ⟨a x * (x : G)⁻¹, hc (hdmem x)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change a ((x : G) * y) * ((x : G) * y)⁻¹ =
        (a x * (x : G)⁻¹) * (a y * (y : G)⁻¹)
      have hy := mem_center_iff.mp (hc (hdmem y)) (x : G)⁻¹
      rw [map_mul, mul_inv_rev]
      calc
        _ = a x * ((a y * (y : G)⁻¹) * (x : G)⁻¹) := by group
        _ = a x * ((x : G)⁻¹ * (a y * (y : G)⁻¹)) := by rw [hy]
        _ = _ := by group }
  have hd : (commutator X).map d = ⊥ := by
    rw [map_commutator_eq]
    exact bot_unique ((commutator_mono le_top le_top).trans
      (show ⁅(⊤ : Subgroup (center G)), ⊤⁆ ≤ ⊥ by rw [← commutator_def, commutator_eq_bot]))
  rintro _ ⟨x, hx, rfl⟩
  have hdx : d x = 1 := mem_bot.mp (hd ▸ mem_map_of_mem d hx)
  have he := congrArg Subtype.val hdx
  exact (mem_fixedSubgroup _ _).mpr (mul_inv_eq_one.mp he)

theorem fixed_commutator_le_image_of_central_ker
    (a : MulAut G) (b : MulAut H) (f : G →* H)
    (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (heq : ∀ x, f (a x) = b (f x)) :
    (commutator b.fixedSubgroup).map b.fixedSubgroup.subtype ≤ a.fixedSubgroup.map f := by
  let X := b.fixedSubgroup.comap f
  let q := f.subgroupComap b.fixedSubgroup
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective _ hf
  have hfix : (commutator X).map X.subtype ≤ a.fixedSubgroup :=
    fixes_commutator_of_central_displacement a f hc X (fun x hx =>
      (heq x).trans ((mem_fixedSubgroup _ _).mp hx))
  have hm : (commutator X).map q = commutator b.fixedSubgroup := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hq, ← commutator_def]
  rw [← hm, map_map]
  change (commutator X).map (f.comp X.subtype) ≤ a.fixedSubgroup.map f
  rw [← map_map]
  exact map_mono hfix
theorem fixed_derived_sylow_card_dvd [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime]
    (a : MulAut G) (b c : MulAut H) (f : G →* H)
    (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (heq : ∀ x, f (a x) = b (f x))
    (P : Sylow p a.fixedSubgroup)
    (hP : ((P : Subgroup a.fixedSubgroup).map a.fixedSubgroup.subtype).map f ≤ c.fixedSubgroup)
    (Q : Sylow p (commutator b.fixedSubgroup)) : Nat.card Q ∣ Nat.card c.fixedSubgroup := by
  let I := a.fixedSubgroup.map f
  let R := P.mapSurjective (f.subgroupMap_surjective a.fixedSubgroup)
  have hR : (R : Subgroup I).map I.subtype =
      ((P : Subgroup a.fixedSubgroup).map a.fixedSubgroup.subtype).map f := by
    change ((P : Subgroup a.fixedSubgroup).map (f.subgroupMap a.fixedSubgroup)).map I.subtype = _
    rw [map_map, map_map]
    rfl
  let S := ((Q : Subgroup (commutator b.fixedSubgroup)).map
    (commutator b.fixedSubgroup).subtype).map b.fixedSubgroup.subtype
  have hSI : S ≤ I := (map_mono (map_subtype_le _)).trans
    (fixed_commutator_le_image_of_central_ker a b f hf hc heq)
  have hs : IsPGroup p (S.subgroupOf I) :=
    ((Q.isPGroup'.map _).map _).comap_subtype
  obtain ⟨U, hU⟩ := hs.exists_le_sylow
  have hd : Nat.card (S.subgroupOf I) ∣ Nat.card R := by
    have hh := card_dvd_of_le hU
    rwa [Nat.card_congr (U.equiv R).toEquiv] at hh
  have hScard : Nat.card (S.subgroupOf I) = Nat.card Q := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSI).toEquiv]
    exact (card_map_of_injective b.fixedSubgroup.subtype_injective).trans
      (card_map_of_injective (commutator b.fixedSubgroup).subtype_injective)
  rw [hScard] at hd
  have hRc : (R : Subgroup I).map I.subtype ≤ c.fixedSubgroup := hR ▸ hP
  have hRcard : Nat.card ((R : Subgroup I).map I.subtype) = Nat.card R :=
    card_map_of_injective I.subtype_injective
  exact hd.trans (hRcard ▸ card_dvd_of_le hRc)

end MulAut
